// Line-at-a-time processing for embedders
//
// SPDX-License-Identifier: MIT
//
// This file is part of the uutils sed package.
// It is licensed under the MIT License.
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

//! Run a sed script over lines an embedder delivers one at a time, such as a
//! shell whose pipeline stages are cooperative tasks and cannot block in a
//! reader. The engine never reads input or writes to the process's stdout.

use crate::sed::command::{Address, Command, CommandData, InputAction, ProcessingContext};
use crate::sed::compiler::compile;
use crate::sed::fast_io::{IOChunk, OutputBuffer};
use crate::sed::named_writer;
use crate::sed::processor::{KnownLast, process_line};
use crate::sed::{build_context, get_scripts_files, normalize_in_place, uu_app};
use std::cell::RefCell;
use std::collections::HashSet;
use std::io::{self, Write};
use std::path::PathBuf;
use std::rc::Rc;
use uucore::error::UResult;

/// What the embedder should do after delivering a line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flow {
    /// Deliver the next line, if any.
    Continue,
    /// `q` or `Q` ran, or `n` found no next line: stop reading input.
    Quit,
}

/// A compiled script with its processing state.
pub struct Engine {
    commands: Option<Rc<RefCell<Command>>>,
    context: ProcessingContext,
    output: OutputBuffer,
    sink: Rc<RefCell<Vec<u8>>>,
    started: bool,
    needs_last: bool,
}

/// Collects the engine's output until the embedder takes it.
struct Sink(Rc<RefCell<Vec<u8>>>);

impl Write for Sink {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(data);
        Ok(data.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Engine {
    /// Parse `args` (the command name first) like `sed`, and compile the
    /// script. Returns the engine and its input operands; `-` names
    /// standard input. The `e` command and `s///e` flag are refused.
    pub fn new(args: impl uucore::Args) -> UResult<(Self, Vec<PathBuf>)> {
        uucore::error::set_exit_code(0);
        let matches = uu_app().try_get_matches_from(normalize_in_place(args))?;
        let (scripts, files) = get_scripts_files(&matches)?;
        let mut context = build_context(&matches)?;
        context.no_exec = true;
        // The embedder presents all operands as one stream.
        context.last_file = true;
        let commands = compile(scripts, &mut context)?;
        let needs_last = uses_last_line(commands.as_ref());
        let sink = Rc::new(RefCell::new(Vec::new()));
        let output = OutputBuffer::from_writer(Box::new(Sink(Rc::clone(&sink))));
        Ok((
            Self {
                commands,
                context,
                output,
                sink,
                started: false,
                needs_last,
            },
            files,
        ))
    }

    /// True for `-i` and `-s`, whose semantics depend on whole, separate
    /// files: run `uumain` over the files instead.
    pub fn needs_files(&self) -> bool {
        self.context.in_place || self.context.separate
    }

    /// The input record delimiter: NUL with `-z`, else newline.
    pub fn delimiter(&self) -> u8 {
        if self.context.null_data { b'\0' } else { b'\n' }
    }

    /// Whether [`Engine::record`] needs to know if a line is the last one
    /// (`$` addresses, `n` and `c`), so the embedder must read one line ahead.
    pub fn needs_last(&self) -> bool {
        self.needs_last
    }

    /// Process one input line, including its delimiter if present, and
    /// append the resulting output to `out`.
    pub fn record(&mut self, line: &[u8], is_last: bool, out: &mut Vec<u8>) -> UResult<Flow> {
        self.start()?;
        let delimiter = self.delimiter();
        let (content, terminated) = match line.split_last() {
            Some((last, content)) if *last == delimiter => (content, true),
            _ => (line, false),
        };
        let pattern = IOChunk::from_bytes(content.to_vec(), terminated);
        process_line(
            self.commands.clone(),
            pattern,
            &mut KnownLast(is_last),
            &mut self.output,
            &mut self.context,
        )?;
        let flow = if self.context.stop_processing {
            self.output.flush_pending_newline()?;
            Flow::Quit
        } else {
            Flow::Continue
        };
        self.take(out)?;
        Ok(flow)
    }

    /// Finish after the last line (or a quit): print a pending `N` line,
    /// flush `w` files, and append any remaining output to `out`.
    pub fn finish(&mut self, out: &mut Vec<u8>) -> UResult<()> {
        self.start()?;
        if !self.context.quiet
            && !self.context.stop_processing
            && let Some(InputAction {
                prepend: Some(mut pending),
                ..
            }) = self.context.input_action.take()
        {
            pending.push(b'\n');
            self.output.write_bytes(&pending)?;
        }
        named_writer::flush_all()?;
        self.take(out)
    }

    /// The exit status set by `q` or `Q`, else 0.
    pub fn exit_code(&self) -> i32 {
        uucore::error::get_exit_code()
    }

    /// Output that zero-address commands (`0r file`) produce before input.
    fn start(&mut self) -> UResult<()> {
        if !self.started {
            self.started = true;
            // As at the start of the first file: pre-latch `0,/re/` ranges.
            crate::sed::processor::reset_latched_address_ranges(&mut self.context.range_commands);
            crate::sed::processor::process_address_0(self.commands.clone(), &mut self.output)?;
        }
        Ok(())
    }

    fn take(&mut self, out: &mut Vec<u8>) -> UResult<()> {
        self.output.flush()?;
        out.append(&mut self.sink.borrow_mut());
        Ok(())
    }
}

/// Whether any reachable command asks if the current line is the last.
fn uses_last_line(first: Option<&Rc<RefCell<Command>>>) -> bool {
    let mut pending: Vec<Rc<RefCell<Command>>> = first.cloned().into_iter().collect();
    let mut seen = HashSet::new();
    while let Some(command) = pending.pop() {
        if !seen.insert(Rc::as_ptr(&command)) {
            continue;
        }
        let command = command.borrow();
        let last = |address: &Option<Address>| matches!(address, Some(Address::Last));
        if last(&command.addr1) || last(&command.addr2) || matches!(command.code, 'n' | 'c') {
            return true;
        }
        if let CommandData::BranchTarget(Some(target)) = &command.data {
            pending.push(Rc::clone(target));
        }
        if let Some(next) = &command.next {
            pending.push(Rc::clone(next));
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(args: &[&str], input: &str) -> (String, i32) {
        let argv: Vec<std::ffi::OsString> = std::iter::once("sed")
            .chain(args.iter().copied())
            .map(Into::into)
            .collect();
        let (mut engine, _) = Engine::new(argv.into_iter()).unwrap();
        let mut out = Vec::new();
        let lines: Vec<&str> = input.split_inclusive('\n').collect();
        for (index, line) in lines.iter().enumerate() {
            let last = index + 1 == lines.len();
            if engine.record(line.as_bytes(), last, &mut out).unwrap() == Flow::Quit {
                break;
            }
        }
        engine.finish(&mut out).unwrap();
        (String::from_utf8(out).unwrap(), engine.exit_code())
    }

    #[test]
    fn substitutes_with_basic_regex_groups() {
        assert_eq!(run(&[r"s/\(a\)\(b\)/\2\1/"], "ab\nxab\n").0, "ba\nxba\n");
    }

    #[test]
    fn next_line_commands_match_gnu() {
        assert_eq!(run(&["n;d"], "a\nb\nc\n").0, "a\nc\n");
        assert_eq!(run(&["-n", "n;p"], "a\nb\nc\n").0, "b\n");
        assert_eq!(run(&["-n", "h;n;G;p"], "a\nb\nc\n").0, "b\na\n");
        assert_eq!(run(&["$!N;s/\\n/+/"], "a\nb\nc\n").0, "a+b\nc\n");
        assert_eq!(run(&["N;s/\\n/+/"], "a\nb\nc\n").0, "a+b\nc\n");
    }

    #[test]
    fn last_line_and_quit() {
        assert_eq!(run(&["-n", "$p"], "a\nb\nc").0, "c");
        let (out, code) = run(&["2q5"], "a\nb\nc\n");
        assert_eq!((out.as_str(), code), ("a\nb\n", 5));
        assert_eq!(run(&["1!G;h;$!d"], "a\nb\n").0, "b\na\n");
        assert_eq!(run(&["0,/b/d"], "a\nb\nc\n").0, "c\n");
    }

    #[test]
    fn gnu_substitution_extensions() {
        assert_eq!(run(&["s/a/A/2g"], "aaaa\n").0, "aAAA\n");
        assert_eq!(
            run(&[r"s/\(\w\+\) \(\w\+\)/\u\1 \U\2\E!/"], "hello world\n").0,
            "Hello WORLD!\n"
        );
        assert_eq!(run(&[r"s/.*/\L\u&/"], "hELLO\n").0, "Hello\n");
    }

    #[test]
    fn locale_override_selects_utf8() {
        crate::sed::set_locale(Some("C.UTF-8".into()));
        assert_eq!(run(&["s/h./H/"], "héllo\n").0, "Hllo\n");
        assert_eq!(run(&["-E", r"s/(ab)\1/X/"], "abab\n").0, "X\n");
        crate::sed::set_locale(None);
    }

    #[test]
    fn exec_is_refused() {
        let argv = ["sed", "s/x/y/e"].map(std::ffi::OsString::from);
        assert!(Engine::new(argv.into_iter()).is_err());
    }
}

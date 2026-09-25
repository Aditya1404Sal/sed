// Compile the scripts into the internal representation of commands
//
// SPDX-License-Identifier: MIT
// Copyright (c) 2025 Diomidis Spinellis
//
// This file is part of the uutils sed package.
// It is licensed under the MIT License.
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::sed::command::{
    Address, CaseConversion, CharacterMode, Command, CommandData, ParsedTransliteration,
    ProcessingContext, RegexMode, ReplacementPart, ReplacementTemplate, Substitution,
    Transliteration,
};
use crate::sed::delimited_parser::{
    os_string_from_bytes, parse_char_escape, parse_regex_for_mode, parse_transliteration_for_mode,
    push_escaped_char,
};
use crate::sed::error_handling::{
    ScriptLocation, compilation_error, location_prefix, remap_unterminated, semantic_error,
};
use crate::sed::fast_regex::Regex;
use crate::sed::named_reader::NamedReader;
use crate::sed::named_writer::NamedWriter;
use crate::sed::script_char_provider::ScriptCharProvider;
use crate::sed::script_line_provider::{ScriptLineProvider, ScriptValue};

use std::cell::RefCell;
use std::mem;
use std::path::PathBuf;
use std::rc::Rc;

use uucore::error::{UResult, USimpleError};

const ERR_ADDRESS_0_USAGE: &str =
    "address 0 can only be used with ~step, a second regular expression, or a read command";
const ERR_SANDBOX: &str = "e/r/w commands disabled in sandbox mode";
const ERR_NO_EXEC: &str =
    "the 'e' command and substitute flag are unsupported here: no shell to run";

const ERR_UNKNOWN_OPTION_TO_S: &str = "unknown option to `s'";
const ERR_TRANSLITERATION_LENGTH: &str = "strings for `y' command are different lengths";
// `compile_sequence` and the post-parse tree walks (`populate_label_map` and friends)
// all use their own heap-allocated work stacks now, not the native call stack, so this
// cap isn't there to protect them. It exists because dropping the compiled `Command`
// chain still isn't: `Command`'s fields (`.next`, and `.data`'s `BranchTarget`) are
// `Rc<RefCell<Command>>`, so Rust's derived drop glue frees a deeply nested chain with
// one native stack frame per level, which measurably overflows the WASI stack somewhere
// between 8,000 and 10,000 levels. 5,000 is comfortably below that, and comfortably
// above any script a person would write by hand.
const MAX_BLOCK_NESTING: usize = 5_000;
const ERR_BLOCK_NESTING_TOO_DEEP: &str = "`{' blocks are nested too deeply";

// Handling required after processing a command
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CommandHandling {
    GetNext,  // Get next command and process that: !
    Return,   // Return from the sequence parser: }
    Continue, // Continue sequence parsing: all other commands
}

/// The type of functions that compile individual commands
type CommandHandler = fn(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling>;

// Command specification
#[derive(Debug, Clone, Copy)]
struct CommandSpec {
    n_addr: usize,           // Number of supported addresses
    handler: CommandHandler, // Argument-specific command compilation handler
}

/// Compile the scripts into an executable data structure.
pub fn compile(
    scripts: Vec<ScriptValue>,
    context: &mut ProcessingContext,
) -> UResult<Option<Rc<RefCell<Command>>>> {
    let mut make_providers = ScriptLineProvider::new(scripts);

    let mut empty_line = ScriptCharProvider::new("");
    let result = compile_sequence(&mut make_providers, &mut empty_line, context)?;

    // Comment-out the following to show the compiled script.
    #[cfg(any())]
    dbg!(&result);

    // Link branch commands to the target label commands.
    populate_label_map(result.clone(), context)?;
    populate_range_commands(result.clone(), context);
    resolve_branch_targets(result.clone(), context)?;

    // Link the ends of command blocks to their following commands.
    // This converts the tree into a graph, so it must be the last
    // conversion that traverses the structure as a tree.
    if context.parsed_block_nesting > 0 {
        // GNU's own wording, verified against the oracle: `sed: -e expression #1, char 0:
        // unmatched `{'` — this fires after `compile_sequence` has already collapsed every
        // open frame at true EOF (see its own comment), so there's no live `ScriptCharProvider`
        // position left to report; `lines`'s own last-active source/line (its `last_input_name`
        // fallback) is still there, and char 0 is GNU's own sentinel here (not a real column).
        return Err(USimpleError::new(
            1,
            format!(
                "{}: unmatched `{{'",
                location_prefix(
                    make_providers.get_input_name(),
                    make_providers.get_line_number(),
                    0
                )
            ),
        ));
    }
    patch_block_endings(result.clone());

    Ok(result)
}

/// For every Command in the top-level `head` chain, look for
/// `CommandData::BranchTarget(Some(sub_head))` '{' commands, and splice each one's tail
/// back to the original "next" pointer of its *parent* (falling back to the parent's own
/// splice target if its own next was `None`).
///
/// Two passes, rather than one recursive walk that splices as it goes (deep nesting
/// would overflow the native stack under WASI): the first only reads `.next` — including
/// each nested block's own `own_next`, which a splice would otherwise overwrite before
/// that block gets its turn — and records every splice this pass would have made; the
/// second applies them. Since a splice never depends on another splice (a block's tail
/// is only ever the target of the one enclosing splice that closes it), any order in the
/// second pass gives the same result as the recursive original.
fn patch_block_endings(head: Option<Rc<RefCell<Command>>>) {
    type Link = Option<Rc<RefCell<Command>>>;
    let mut writes: Vec<(Rc<RefCell<Command>>, Link)> = Vec::new();
    // (chain to walk, that chain's own fallback splice target)
    let mut pending: Vec<(Link, Link)> = vec![(head, None)];
    while let Some((mut cur, parent_next)) = pending.pop() {
        while let Some(rc_cmd) = cur {
            // A read-only borrow: this pass never mutates `.next`.
            let cmd = rc_cmd.borrow();
            // Save this node’s own next pointer
            let own_next = cmd.next.clone();
            // Decide what “splice target” to use:
            //   - if this node has its own_next, use that
            //   - otherwise, fall back to parent_next
            let splice_target = own_next.clone().or_else(|| parent_next.clone());

            // If it has a sub-block, record its tail's splice and queue its body to have
            // its own nested blocks' splices recorded.
            if let CommandData::BranchTarget(Some(ref sub_head)) = cmd.data
                && cmd.code == '{'
            {
                // find the tail of that sub-chain
                let mut tail = sub_head.clone();
                loop {
                    let next_in_sub = tail.borrow().next.clone();
                    match next_in_sub {
                        Some(n) => tail = n,
                        None => break,
                    }
                }

                writes.push((tail, splice_target.clone()));
                pending.push((Some(sub_head.clone()), splice_target));
            }

            // drop the borrow before moving on
            drop(cmd);

            // advance to the next sibling in this level
            cur = own_next;
        }
    }

    for (tail, target) in writes {
        tail.borrow_mut().next = target;
    }
}

/// Populate the context's label map with references to associated commands. Descends
/// into `{`-nested chains with an explicit worklist rather than recursing (deep nesting
/// would otherwise overflow the native stack under WASI), pushing each nested chain to
/// visit later instead of visiting it immediately.
fn populate_label_map(
    head: Option<Rc<RefCell<Command>>>,
    context: &mut ProcessingContext,
) -> UResult<()> {
    let mut pending = vec![head];
    while let Some(mut cur) = pending.pop() {
        while let Some(rc_cmd) = cur.take() {
            // Borrow mutably just long enough to inspect/rewire this node
            let cmd = rc_cmd.borrow_mut();

            // Extract any label to insert after borrow ends
            let maybe_label = match &cmd.data {
                CommandData::BranchTarget(Some(sub_head)) => {
                    pending.push(Some(sub_head.clone()));
                    None
                }
                CommandData::Label(Some(label)) => Some(label.clone()),
                _ => None,
            };

            if let Some(label) = maybe_label
                && cmd.code == ':'
            {
                if context.label_to_command_map.contains_key(&label) {
                    return semantic_error(&cmd.location, format!("duplicate label `{label}'"));
                }
                context.label_to_command_map.insert(label, rc_cmd.clone());
            }

            cur.clone_from(&cmd.next);
        }
    }
    Ok(())
}

/// Populate the context's address range command list with references to associated
/// commands. See [`populate_label_map`] for why `{`-nested chains go on a worklist
/// instead of a recursive call.
fn populate_range_commands(head: Option<Rc<RefCell<Command>>>, context: &mut ProcessingContext) {
    let mut pending = vec![head];
    while let Some(mut cur) = pending.pop() {
        while let Some(rc_cmd) = cur.take() {
            // Borrow mutably just long enough to inspect/rewire this node
            let cmd = rc_cmd.borrow_mut();

            if let CommandData::BranchTarget(Some(sub_head)) = &cmd.data {
                pending.push(Some(Rc::clone(sub_head)));
            }

            if cmd.addr2.is_some() {
                // Save detected range command.
                context.range_commands.push(Rc::clone(&rc_cmd));
            }

            cur.clone_from(&cmd.next);
        }
    }
}

/// Replace branch labels with references to the corresponding commands.
/// Raise an error on undefined labels. See [`populate_label_map`] for why `{`-nested
/// chains go on a worklist instead of a recursive call.
fn resolve_branch_targets(
    head: Option<Rc<RefCell<Command>>>,
    context: &mut ProcessingContext,
) -> UResult<()> {
    let mut pending = vec![head];
    while let Some(mut cur) = pending.pop() {
        while let Some(rc_cmd) = cur.take() {
            // Borrow mutably just long enough to inspect/rewire this node
            let mut cmd = rc_cmd.borrow_mut();

            if let CommandData::BranchTarget(Some(sub_head)) = &cmd.data {
                pending.push(Some(sub_head.clone()));
            }

            // Only for 't', 'T', or 'b' commands:
            if matches!(cmd.code, 't' | 'T' | 'b') {
                // Take ownership of the current data
                let old_data = mem::replace(&mut cmd.data, CommandData::None);

                // Build the replacement
                let new_data = match old_data {
                    CommandData::Label(Some(label)) => {
                        let target = context
                            .label_to_command_map
                            .get(&label)
                            .cloned()
                            .ok_or_else(|| {
                                semantic_error::<()>(
                                    &cmd.location,
                                    format!("undefined label `{label}'"),
                                )
                                .unwrap_err()
                            })?;
                        CommandData::BranchTarget(Some(target))
                    }
                    CommandData::Label(None) => CommandData::BranchTarget(None),
                    other => other, // put back anything else unchanged
                };

                // Store it back
                cmd.data = new_data;
            }

            // Advance to the next sibling
            cur.clone_from(&cmd.next);
        }
    }
    Ok(())
}

/// Compile provided scripts into a sequence of commands.
/// One `{ ... }` nesting level's partial command list, plus (for every level but the
/// outermost) the `{` command whose `BranchTarget` gets this level's head once it closes.
struct CompileFrame {
    head: Option<Rc<RefCell<Command>>>,
    tail: Option<Rc<RefCell<Command>>>,
    opener: Option<Rc<RefCell<Command>>>,
}

impl CompileFrame {
    fn link(&mut self, cmd: Rc<RefCell<Command>>) {
        if let Some(ref t) = self.tail {
            t.borrow_mut().next = Some(cmd.clone());
        } else {
            self.head = Some(cmd.clone());
        }
        self.tail = Some(cmd);
    }
}

/// Compile a `{ ... }`-nested sequence of commands. `{` and `}` push and pop a frame on
/// `stack` instead of recursing natively: GNU sed's own compiler doesn't recurse for
/// nesting either, and a few thousand levels (well within what one `sed -f` script might
/// contain) would overflow a native call stack under WASI, where a Golem agent has no
/// way to recover from that trap.
fn compile_sequence(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    context: &mut ProcessingContext,
) -> UResult<Option<Rc<RefCell<Command>>>> {
    let mut stack = vec![CompileFrame {
        head: None,
        tail: None,
        opener: None,
    }];

    loop {
        line.eat_spaces();

        // Special first-line comment disabling default output
        // According to POSIX: "If the first two characters in the script are
        // "#n", the default output shall be suppressed".
        if !line.eol()
            && line.current() == '#'
            && lines.get_line_number() == 1
            && line.get_pos() == 0
        {
            line.advance();
            if !line.eol() && line.current() == 'n' {
                context.quiet = true;
            }
            // Ignore rest of line
            while !line.eol() {
                line.advance();
            }
        }

        // Empty lines and comments
        if line.eol() || line.current() == '#' {
            match lines.next_line()? {
                None => {
                    // EOF: collapse every open frame (as recursive returns would have,
                    // one level at a time), so an unmatched `{` still just gives back a
                    // partial tree — `compile()`'s `parsed_block_nesting` check is what
                    // turns that into "unmatched `{'".
                    while stack.len() > 1 {
                        let finished = stack.pop().unwrap();
                        if let Some(opener) = &finished.opener {
                            opener.borrow_mut().data = CommandData::BranchTarget(finished.head);
                        }
                    }
                    return Ok(stack.pop().unwrap().head);
                }
                Some(line_bytes) => {
                    *line = ScriptCharProvider::new(line_bytes);
                }
            }
            continue;
        } else if line.current() == ';' {
            line.advance();
            continue;
        }

        let mut cmd = Rc::new(RefCell::new(Command::at_position(lines, line)));
        let n_addr = compile_address_range(lines, line, &mut cmd, context)?;
        line.eat_spaces();
        let mut cmd_spec = get_verified_cmd_spec(lines, line, n_addr, context.posix)?;
        // Compile the command according to its specification.
        let mut cmd_mut = cmd.borrow_mut();
        cmd_mut.code = line.current();
        match (cmd_spec.handler)(lines, line, &mut cmd_mut, context)? {
            CommandHandling::GetNext => {
                cmd_spec = get_verified_cmd_spec(lines, line, n_addr, context.posix)?;
                cmd_mut.code = line.current();
                (cmd_spec.handler)(lines, line, &mut cmd_mut, context)?;
            }
            CommandHandling::Return => {
                // `}`: close the innermost frame and resume filling its parent. The `}`
                // command itself is never linked into any list (it carries no data).
                drop(cmd_mut);
                let finished = stack.pop().ok_or_else(|| {
                    compilation_error::<()>(lines, line, "unexpected `}'").unwrap_err()
                })?;
                if let Some(opener) = &finished.opener {
                    opener.borrow_mut().data = CommandData::BranchTarget(finished.head);
                }
                continue;
            }
            CommandHandling::Continue => (),
        }
        let opens_block = cmd_mut.code == '{';
        drop(cmd_mut);

        stack.last_mut().unwrap().link(cmd.clone());
        if opens_block {
            // `{`: everything up to the matching `}` belongs to a new, inner frame;
            // `cmd`'s `BranchTarget` is filled in (replacing the `None` placeholder
            // `compile_block_command` left) when that frame closes above.
            stack.push(CompileFrame {
                head: None,
                tail: None,
                opener: Some(cmd),
            });
        }
    }
}

/// Return true if c is a valid character for specifying a context address
fn is_address_char(c: char) -> bool {
    matches!(c, '0'..='9' | '/' | '\\' | '$')
}

/// Compile a command's optional address range into cmd.
/// Return the number of addresses encountered.
fn compile_address_range(
    lines: &ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Rc<RefCell<Command>>,
    context: &ProcessingContext,
) -> UResult<usize> {
    let mut n_addr = 0;
    let mut cmd = cmd.borrow_mut();

    let mut is_line0 = false;

    line.eat_spaces();
    if !line.eol() && is_address_char(line.current()) {
        let addr1 = compile_address(lines, line, context)?;
        is_line0 = matches!(addr1, Address::Line(0));
        cmd.addr1 = Some(addr1);
        if is_line0 && context.posix {
            // 0 starting address is a GNU extension.
            return compilation_error(lines, line, "address 0 is invalid in POSIX mode");
        }
        n_addr += 1;
    }

    line.eat_spaces();
    if n_addr == 1 && !line.eol() && matches!(line.current(), ',' | '~') {
        let separator = line.current();
        let is_step_match = separator == '~'; // E.g. 0~2: Pick even-numbered lines
        line.advance();
        line.eat_spaces();
        let is_step_end = if !line.eol() && line.current() == '~' {
            // E.g. /foo/,~10: Start at foo, include all lines until multiple of 10 is reached.
            line.advance();
            line.eat_spaces();
            true
        } else {
            false
        };

        if (is_step_match || is_step_end) && context.posix {
            // ~ steps are a GNU extension.
            return compilation_error(lines, line, "~step is invalid in POSIX mode");
        }

        // Look for second address.
        if !line.eol() {
            // Same as `is_address_char`, plus `+`: `compile_address` accepts a leading `+`
            // for a *second* address (`/re/,+N`) that `is_address_char` doesn't need to know
            // about, since a first address can't start with one.
            if !is_address_char(line.current()) && line.current() != '+' {
                // GNU's own wording, verified against the oracle (`1,d` -> "unexpected `,'",
                // pointing at the separator that promised a second address, not whatever
                // invalid character follows it) — this used to reach `compile_address`'s own
                // catch-all `_ => panic!("invalid context address")` and crash instead.
                return compilation_error(lines, line, format!("unexpected `{separator}'"));
            }
            let addr2 = compile_address(lines, line, context)?;
            // Set step_n to the number specified in the (required numeric) address.
            let step_n = if is_step_match || is_step_end {
                match addr2 {
                    Address::Line(n) => n,
                    _ => {
                        return compilation_error(
                            lines,
                            line,
                            "~step can only be specified through numeric values",
                        );
                    }
                }
            } else {
                0 // dummy, not used
            };

            if is_line0 && !matches!(addr2, Address::Re(_)) && !is_step_match {
                return compilation_error(lines, line, ERR_ADDRESS_0_USAGE);
            }

            // If needed, transform Address::Line into Address::Step*.
            cmd.addr2 = if is_step_match {
                Some(Address::StepMatch(step_n))
            } else if is_step_end {
                Some(Address::StepEnd(step_n))
            } else {
                Some(addr2)
            };
            n_addr += 1;
        }
    }

    // Zero-address read command check
    if is_line0 && n_addr == 1 {
        // After retrieval of first address, subsequent spaces
        // are consumed unconditionally. By now, the position
        // must be in non-whitespace character or EOL.
        if line.eol() || line.current() != 'r' {
            return compilation_error(lines, line, ERR_ADDRESS_0_USAGE);
        }
    }

    Ok(n_addr)
}

/// Read the line's remaining characters as a file path and return it.
// TODO Move to delimited_parser in separate commit.
fn read_file_path(lines: &ScriptLineProvider, line: &mut ScriptCharProvider) -> UResult<PathBuf> {
    line.advance(); // Skip the command/w character
    line.eat_spaces(); // Skip any leading whitespace

    let mut path = Vec::new();
    while !line.eol() {
        path.push(line.current_byte());
        line.advance();
    }

    if path.is_empty() {
        compilation_error(lines, line, "missing filename in r/R/w/W commands")
    } else {
        os_string_from_bytes(path).map(PathBuf::from).map_err(|e| {
            compilation_error::<PathBuf>(lines, line, format!("invalid characters file path: {e}"))
                .unwrap_err()
        })
    }
}

/// Compile and return a single range address specification.
// Due to their irregular syntax ~ addresses are returned as Line() and adjusted
// in compile_address_range().
fn compile_address(
    lines: &ScriptLineProvider,
    line: &mut ScriptCharProvider,
    context: &ProcessingContext,
) -> UResult<Address> {
    let mut icase = false;

    if line.eol() {
        return compilation_error(lines, line, "expected context address");
    }

    match line.current() {
        '\\' | '/' => {
            // Regular expression
            if line.current() == '\\' {
                // The next character is an arbitrary delimiter
                line.advance();
            }
            let regex_mode = if context.regex_extended {
                RegexMode::Extended
            } else {
                RegexMode::Basic
            };
            let re = remap_unterminated(
                parse_regex_for_mode(
                    lines,
                    line,
                    regex_mode,
                    context.character_mode,
                    context.posix,
                ),
                "unterminated address regex",
            )?;
            // Skip over delimiter
            line.advance();

            line.eat_spaces();
            if !line.eol() && line.current() == 'I' {
                icase = true;
                line.advance();
            }

            Ok(Address::Re(compile_regex(
                lines, line, &re, context, icase, false,
            )?))
        }
        '$' => {
            line.advance();
            Ok(Address::Last)
        }
        '+' => {
            line.advance();
            let number = parse_number(lines, line, true)?.unwrap();
            Ok(Address::RelLine(number))
        }
        c if c.is_ascii_digit() => {
            let number = parse_number(lines, line, true)?.unwrap();
            Ok(Address::Line(number))
        }
        _ => panic!("invalid context address"),
    }
}

/// Parse and return the decimal number at the current line position.
/// Advance the line to first non-digit or EOL.
/// Issue an error if the number is required.
fn parse_number(
    lines: &ScriptLineProvider,
    line: &mut ScriptCharProvider,
    required: bool,
) -> UResult<Option<usize>> {
    let mut num_str = String::new();

    while !line.eol() && line.current().is_ascii_digit() {
        num_str.push(line.current());
        line.advance();
    }

    if num_str.is_empty() {
        if required {
            return compilation_error(lines, line, "number expected");
        }
        return Ok(None);
    }

    num_str
        .parse::<usize>()
        .map_err(|_| format!("invalid number '{num_str}'"))
        .map_err(|msg| compilation_error::<usize>(lines, line, msg).unwrap_err())
        .map(Some)
}

/// Parse the end of a command, failing with an error on extra characters.
fn parse_command_ending(
    lines: &ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
) -> UResult<()> {
    if !line.eol() && line.current() == ';' {
        line.advance();
        return Ok(());
    }

    if !line.eol() && line.current() == '}' {
        return Ok(());
    }

    if !line.eol() {
        return compilation_error(
            lines,
            line,
            format!("extra characters at the end of the {} command", cmd.code),
        );
    }

    Ok(())
}

/// Convert a primitive BRE pattern to a safe ERE-compatible pattern.
/// - Replaces `\(`, `\)`, `\?`, `\+`, `\|`, `\{` and `\}` with `(`, `)`, `?`, `+`, `|`, `{` and `}`.
/// - Puts single-digit back-references in non-capturing groups..
/// - Escapes ERE-only metacharacters: `+ ? { } | ( )`.
/// - Leaves all other bytes as-is.
fn bre_to_ere(pattern: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(pattern.len());
    let mut pos = 0;

    let mut at_beginning = true;
    let mut previous: Option<u8> = None;
    while pos < pattern.len() {
        let c = pattern[pos];
        pos += 1;

        if c == b'\\' {
            match pattern.get(pos).copied() {
                Some(b'(') => {
                    pos += 1;
                    result.push(b'('); // Group start
                }
                Some(b')') => {
                    pos += 1;
                    result.push(b')'); // Group end
                }
                Some(b'?') => {
                    pos += 1;
                    result.push(b'?'); // Quantifier 0 or 1
                }
                Some(b'+') => {
                    pos += 1;
                    result.push(b'+'); // Quantifier 1 or more
                }
                Some(b'|') => {
                    pos += 1;
                    result.push(b'|'); // Alternation operator
                }
                Some(b'{') => {
                    pos += 1;
                    result.push(b'{'); // Brace quantifier start
                }
                Some(b'}') => {
                    pos += 1;
                    result.push(b'}'); // Brace quantifier end
                }
                Some(v) if v.is_ascii_digit() => {
                    // Back-reference.  In sed BREs these are single-digit
                    // (\1-\9) whereas fancy_regex supports multi-digit
                    // back-references. Put them in a non-capturing group
                    // to avoid having the number extend beyond the single
                    // digit. Example: In sed \11 matches group 1 followed
                    // by '1', not group 11.
                    result.extend_from_slice(b"(?:\\");
                    result.push(v);
                    result.push(b')');
                    pos += 1;
                }
                Some(next) => {
                    // Preserve other escaped characters.
                    pos += 1;
                    result.push(b'\\');
                    result.push(next);
                }
                None => {
                    // Trailing backslash; keep it.
                    result.push(b'\\');
                }
            }
        } else {
            match c {
                b'+' | b'?' | b'{' | b'}' | b'|' | b'(' | b')' => {
                    // Escape unsupported ERE metacharacters.
                    result.push(b'\\');
                    result.push(c);
                }
                b'^' if !at_beginning && previous != Some(b'[') => {
                    // In BREs ^ has special meaning at the beginning
                    // and as bracket negation.  This heuristic escapes
                    // all other uses, which per POSIX are valid in EREs.
                    // "the ERE "a^b" is valid, but can never match because
                    // the 'a' prevents the expression "^b" from matching
                    // starting at the first character."
                    // POSIX 9.4.9 ERE Expression Anchoring
                    result.push(b'\\');
                    result.push(c);
                }
                b'$' if pos < pattern.len() => {
                    // Similarly for $ appearing not at the end.
                    result.push(b'\\');
                    result.push(c);
                }
                _ => result.push(c),
            }
        }
        at_beginning = false;
        previous = Some(c);
    }

    result
}

/// Compile the provided regular expression string into a corresponding engine.
/// An empty pattern results in None, which means that the last RE employed
/// at runtime will be used.
fn compile_regex(
    lines: &ScriptLineProvider,
    line: &ScriptCharProvider,
    pattern: impl AsRef<[u8]>,
    context: &ProcessingContext,
    icase: bool,
    multiline: bool,
) -> UResult<Option<Regex>> {
    let pattern = pattern.as_ref();
    if pattern.is_empty() {
        return Ok(None);
    }

    // Convert basic to extended regular expression if needed.
    let pattern = if context.regex_extended {
        pattern.to_vec()
    } else {
        bre_to_ere(pattern)
    };

    // Add any required modifiers.
    let mut modifiers = Vec::new();
    if icase {
        modifiers.push(b'i');
    }
    if multiline {
        modifiers.push(b'm');
    }
    let pattern = if modifiers.is_empty() {
        pattern
    } else {
        // Append modifiers.
        let mut with_modifiers = Vec::with_capacity(pattern.len() + modifiers.len() + 3);
        with_modifiers.extend_from_slice(b"(?");
        with_modifiers.extend_from_slice(&modifiers);
        with_modifiers.push(b')');
        with_modifiers.extend_from_slice(&pattern);
        with_modifiers
    };

    // Compile into engine.
    let compiled = Regex::new(&pattern, context.character_mode).map_err(|e| {
        compilation_error::<Regex>(
            lines,
            line,
            format!("invalid regex '{}': {e}", String::from_utf8_lossy(&pattern)),
        )
        .unwrap_err()
    })?;

    Ok(Some(compiled))
}

/// Compile a regular expression replacement string according to character mode.
pub fn compile_replacement(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    character_mode: CharacterMode,
) -> UResult<ReplacementTemplate> {
    let mut parts = Vec::new();
    let mut literal = Vec::new();

    let delimiter = line.current();
    line.advance();

    loop {
        while !line.eol() {
            match line.current() {
                '\\' => {
                    line.advance();

                    // Line input_action
                    if line.eol() {
                        if let Some(next_line) = lines.next_line()? {
                            literal.push(b'\n');
                            *line = ScriptCharProvider::new(next_line);
                            continue;
                        }
                        return compilation_error(lines, line, "unterminated `s' command");
                    }

                    match line.current() {
                        // \0 - \9
                        c @ '0'..='9' => {
                            let ref_num = c.to_digit(10).unwrap();

                            if !literal.is_empty() {
                                parts.push(ReplacementPart::Literal(std::mem::take(&mut literal)));
                            }
                            if ref_num == 0 {
                                parts.push(ReplacementPart::WholeMatch);
                            } else {
                                parts.push(ReplacementPart::Group(ref_num));
                            }
                            line.advance();
                        }

                        // Literal \ and &
                        '\\' | '&' => {
                            literal.push(line.current_byte());
                            line.advance();
                        }

                        // GNU case conversion
                        c @ ('U' | 'L' | 'u' | 'l' | 'E') => {
                            if !literal.is_empty() {
                                parts.push(ReplacementPart::Literal(std::mem::take(&mut literal)));
                            }
                            parts.push(ReplacementPart::Case(match c {
                                'U' => CaseConversion::Upper,
                                'L' => CaseConversion::Lower,
                                'u' => CaseConversion::UpperNext,
                                'l' => CaseConversion::LowerNext,
                                _ => CaseConversion::End,
                            }));
                            line.advance();
                        }

                        // Literal delimiter
                        v if v == delimiter => {
                            literal.push(line.current_byte());
                            line.advance();
                        }

                        // other escape sequences
                        _ => {
                            if let Some(decoded) = parse_char_escape(line) {
                                push_escaped_char(&mut literal, decoded, character_mode);
                            } else {
                                literal.push(b'\\');
                                literal.push(line.current_byte());
                                line.advance();
                            }
                        }
                    }
                }

                '&' => {
                    if !literal.is_empty() {
                        parts.push(ReplacementPart::Literal(std::mem::take(&mut literal)));
                    }
                    parts.push(ReplacementPart::WholeMatch);
                    line.advance();
                }

                '\n' => {
                    return compilation_error(
                        lines,
                        line,
                        "unescaped newline inside substitute replacement",
                    );
                }

                c if c == delimiter => {
                    line.advance(); // skip closing delimiter
                    if !literal.is_empty() {
                        parts.push(ReplacementPart::Literal(literal));
                    }
                    return Ok(ReplacementTemplate::new(parts));
                }

                _ => {
                    literal.push(line.current_byte());
                    line.advance();
                }
            }
        }

        // Fetch next line for continued replacement string
        if let Some(next_line) = lines.next_line()? {
            *line = ScriptCharProvider::new(next_line);
        } else {
            return compilation_error(lines, line, "unterminated `s' command");
        }
    }
}

// Handles s
fn compile_subst_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance(); // move past 's'

    // `s` with nothing after it (not even a delimiter) — GNU's own wording, verified against
    // the oracle. Used to reach `line.current()` right below with nothing left to look at and
    // panic (index out of bounds) instead.
    if line.eol() {
        return compilation_error(lines, line, "unterminated `s' command");
    }

    let delimiter = line.current();
    if delimiter == '\0' || delimiter == '\\' {
        return compilation_error(
            lines,
            line,
            "substitute pattern cannot be delimited by newline or backslash",
        );
    }

    let regex_mode = if context.regex_extended {
        RegexMode::Extended
    } else {
        RegexMode::Basic
    };
    let pattern = remap_unterminated(
        parse_regex_for_mode(
            lines,
            line,
            regex_mode,
            context.character_mode,
            context.posix,
        ),
        "unterminated `s' command",
    )?;
    let mut subst = Box::new(Substitution::default());

    subst.replacement = compile_replacement(lines, line, context.character_mode)?;
    compile_subst_flags(lines, line, &mut subst, context.posix, context.sandbox)?;
    if subst.execute && context.no_exec {
        return compilation_error(lines, line, ERR_NO_EXEC);
    }

    if pattern.is_empty() && (subst.ignore_case || subst.multiline) {
        return compilation_error(
            lines,
            line,
            "cannot specify modifiers on an empty regular expression",
        );
    }

    // Compile regex with now known modifier flags.
    subst.regex = compile_regex(
        lines,
        line,
        &pattern,
        context,
        subst.ignore_case,
        subst.multiline,
    )?;

    // Catch invalid group references at compile time, if possible.
    if let Some(regex) = &subst.regex
        && subst.replacement.max_group_number > regex.captures_len() - 1
    {
        return compilation_error(
            lines,
            line,
            format!(
                "invalid reference \\{} on `s' command's RHS",
                subst.replacement.max_group_number
            ),
        );
    }
    cmd.data = CommandData::Substitution(subst);

    parse_command_ending(lines, line, cmd)?;
    Ok(CommandHandling::Continue)
}

// Handles y
fn compile_trans_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance(); // move past 'y'

    let delimiter = line.current();
    if delimiter == '\0' || delimiter == '\\' {
        return compilation_error(
            lines,
            line,
            "transliteration string cannot be delimited by newline or backslash",
        );
    }

    let source = parse_transliteration_for_mode(lines, line, context.character_mode)?;
    let target = parse_transliteration_for_mode(lines, line, context.character_mode)?;
    let transliteration = match (source, target) {
        (ParsedTransliteration::Bytes(source), ParsedTransliteration::Bytes(target)) => {
            if source.len() != target.len() {
                return compilation_error(lines, line, ERR_TRANSLITERATION_LENGTH);
            }
            Box::new(Transliteration::from_bytes(&source, &target))
        }
        (ParsedTransliteration::Text(source), ParsedTransliteration::Text(target)) => {
            if source.chars().count() != target.chars().count() {
                return compilation_error(lines, line, ERR_TRANSLITERATION_LENGTH);
            }
            Box::new(Transliteration::from_strings(&source, &target))
        }
        _ => unreachable!("transliteration parser returned mixed modes"),
    };
    cmd.data = CommandData::Transliteration(transliteration);

    line.advance(); // move past last delimiter
    parse_command_ending(lines, line, cmd)?;
    Ok(CommandHandling::Continue)
}

/// Parse the substitution command's optional flags
pub fn compile_subst_flags(
    lines: &ScriptLineProvider,
    line: &mut ScriptCharProvider,
    subst: &mut Substitution,
    posix: bool,
    sandbox: bool,
) -> UResult<()> {
    // GNU: `g` with a number N replaces the Nth match and every later one.
    let mut seen_g = false;
    let mut seen_n = false;

    subst.occurrence = 1; // default
    subst.global = false;
    subst.print_flag = false;
    subst.p_before_e = false;
    subst.ignore_case = false;
    subst.execute = false;
    subst.multiline = false;
    subst.write_file = None;

    loop {
        line.eat_spaces();
        if line.eol() {
            break;
        }

        match line.current() {
            'g' => {
                if seen_g {
                    return compilation_error(lines, line, "multiple `g' options to `s' command");
                }
                seen_g = true;
                line.advance();
            }

            'p' => {
                subst.print_flag = true;
                // 'p' is applied before 'e' iff 'e' has not been seen yet.
                subst.p_before_e = !subst.execute;
                line.advance();
            }

            'i' | 'I' => {
                if posix {
                    return compilation_error(lines, line, ERR_UNKNOWN_OPTION_TO_S);
                }
                subst.ignore_case = true;
                line.advance();
            }

            'm' | 'M' => {
                if posix {
                    return compilation_error(lines, line, ERR_UNKNOWN_OPTION_TO_S);
                }
                subst.multiline = true;
                line.advance();
            }

            'e' => {
                if posix || sandbox {
                    return compilation_error(
                        lines,
                        line,
                        "the 'e' substitute flag is not allowed with --posix or --sandbox",
                    );
                }
                subst.execute = true;
                line.advance();
            }

            _c @ '1'..='9' => {
                if seen_n {
                    return compilation_error(lines, line, "multiple `g' options to `s' command");
                }

                let mut number = 0usize;
                while !line.eol() && line.current().is_ascii_digit() {
                    number = number
                        .checked_mul(10)
                        .and_then(|n| n.checked_add(line.current().to_digit(10).unwrap() as usize))
                        .ok_or_else(|| {
                            compilation_error::<()>(
                                lines,
                                line,
                                "overflow in numeric substitute flag",
                            )
                            .unwrap_err()
                        })?;
                    line.advance();
                }

                subst.occurrence = number;
                seen_n = true;
            }

            'w' => {
                if sandbox {
                    return compilation_error(lines, line, ERR_SANDBOX);
                }
                let location = ScriptLocation::at_position(lines, line);
                let path = read_file_path(lines, line)?;
                subst.write_file = Some(NamedWriter::new(path, location)?);
                break; // 'w' is the last flag allowed
            }

            ';' | '\n' => break,

            _ => {
                return compilation_error(lines, line, ERR_UNKNOWN_OPTION_TO_S.to_string());
            }
        }
    }

    if seen_g {
        if subst.occurrence <= 1 {
            subst.occurrence = 0;
        } else {
            subst.global = true;
        }
    }
    Ok(())
}

// Handles }
fn compile_end_group_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    if context.parsed_block_nesting == 0 {
        return compilation_error(lines, line, "unexpected `}'");
    }
    context.parsed_block_nesting -= 1;
    line.advance();
    line.eat_spaces();
    parse_command_ending(lines, line, cmd)?;
    Ok(CommandHandling::Return)
}

// Handles !
fn compile_negation_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    _context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance();
    line.eat_spaces();
    if cmd.non_select {
        return compilation_error(lines, line, "multiple `!'s");
    }
    cmd.non_select = true;
    Ok(CommandHandling::GetNext)
}

/// Compile a command that doesn't take any arguments
// Handles d D g G h H l n N p P q x =
fn compile_empty_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    _context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance(); // Skip the command character
    line.eat_spaces(); // Skip any trailing whitespace

    parse_command_ending(lines, line, cmd)?;
    Ok(CommandHandling::Continue)
}

// Handles r
fn compile_read_file_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    if context.sandbox {
        return compilation_error(lines, line, ERR_SANDBOX);
    }
    let path = read_file_path(lines, line)?;
    // Unlike `w`/`R`, which open their file right away, `r`'s file is only read when the
    // command runs — possibly long after compilation, and (for an embedder) possibly
    // against a process working directory that no longer matches whatever was current
    // when this script was compiled. Make the path absolute now, against the directory
    // that is current right now, so a later read isn't at the mercy of that.
    let path = if path.is_absolute() {
        path
    } else {
        std::env::current_dir().map_or(path.clone(), |cwd| cwd.join(&path))
    };
    cmd.data = CommandData::Path(path);
    Ok(CommandHandling::Continue)
}

// Handles w
fn compile_write_file_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    if context.sandbox {
        return compilation_error(lines, line, ERR_SANDBOX);
    }
    let location = ScriptLocation::at_position(lines, line);
    let path = read_file_path(lines, line)?;
    cmd.data = CommandData::NamedWriter(NamedWriter::new(path, location)?);
    Ok(CommandHandling::Continue)
}

// Handles R (GNU): like 'r', but queues one line from `path` per invocation instead of
// the whole file. A missing or unreadable file behaves as empty, never an error.
fn compile_read_line_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    if context.sandbox {
        return compilation_error(lines, line, ERR_SANDBOX);
    }
    let path = read_file_path(lines, line)?;
    cmd.data = CommandData::NamedReader(Rc::new(RefCell::new(NamedReader::new(path))));
    Ok(CommandHandling::Continue)
}

// Handles {
// `compile_sequence` special-cases `{` itself (it must push a new frame onto its own
// frame stack rather than recurse), so this handler only does the two things that must
// happen exactly where `{` is consumed: skip past it and count the nesting for
// `compile_end_group_command`'s "unexpected `}'" check. `cmd.data` is filled in once the
// matching `}` (or EOF) closes the frame; `compile_sequence` leaves it as `BranchTarget
// (None)` (an empty block) until then.
fn compile_block_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance(); // move past '{'
    context.parsed_block_nesting += 1;
    if context.parsed_block_nesting > MAX_BLOCK_NESTING {
        return compilation_error(lines, line, ERR_BLOCK_NESTING_TOO_DEEP);
    }
    cmd.data = CommandData::BranchTarget(None);
    Ok(CommandHandling::Continue)
}

// Handles b, t, :
fn compile_label_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    _context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    /// Return true if `c` is in the POSIX portable filename character set.
    fn is_portable_filename_char(c: char) -> bool {
        c.is_ascii_alphanumeric()  // A–Z, a–z, 0–9
        || matches!(c, '.' | '_' | '-')
    }

    line.advance(); // Skip the command character
    line.eat_spaces(); // Skip any leading whitespace

    let mut label = String::new();
    while !line.eol() && is_portable_filename_char(line.current()) {
        label.push(line.current());
        line.advance();
    }

    if label.is_empty() {
        if cmd.code == ':' {
            return compilation_error(lines, line, "empty label");
        }
        cmd.data = CommandData::Label(None);
    } else {
        cmd.data = CommandData::Label(Some(label));
    }

    line.eat_spaces(); // Skip any trailing whitespace
    parse_command_ending(lines, line, cmd)?;
    Ok(CommandHandling::Continue)
}

/// Compile commands that take a number as an argument.
// Handles l q Q
fn compile_number_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance(); // Skip the command character
    line.eat_spaces(); // Skip any leading whitespace

    match parse_number(lines, line, false)? {
        Some(n) => {
            cmd.data = CommandData::Number(n);
        }
        None => match cmd.code {
            'q' | 'Q' => {
                cmd.data = CommandData::Number(0);
            }
            'l' => {
                // A bare `l` wraps at the `-l N` length (default 70), never at the
                // controlling terminal's width: GNU sed's line-wrap length is not
                // terminal-dependent.
                cmd.data = CommandData::Number(context.length);
            }
            _ => panic!("invalid number-expecting command"),
        },
    }

    line.eat_spaces(); // Skip any trailing whitespace
    parse_command_ending(lines, line, cmd)?;
    Ok(CommandHandling::Continue)
}

/// Compile commands that take text as an argument.
// Handles a, c, i
// According to POSIX, these commands expect \ followed by text.
// As a GNU extension the initial \ can be ommitted, and from then on
// character escapes are honored.
fn compile_text_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    line.advance(); // Skip the command character.
    line.eat_spaces(); // Skip any leading whitespace.
    if context.posix {
        compile_text_command_posix(lines, line, cmd, context)
    } else {
        compile_text_command_gnu(lines, line, cmd, context)
    }
}

/// Compile commands that take text as an argument (GNU syntax).
// Handles a, c, i; after the command and initial whitespace have been consumed.
// According to POSIX, these commands expect \ followed by text.
// As a GNU extension the initial \ can be ommitted, and from then on
// character escapes are honored.
fn compile_text_command_gnu(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    // True after a \ at the end of a line
    let mut escaped_newline = false;

    if line.eol() {
        return compilation_error(lines, line, "expected \\ after `a', `c' or `i'".to_string());
    }

    // Skip optional \.
    if !line.eol() && line.current() == '\\' {
        line.advance();
        escaped_newline = line.eol();
    }

    // Gather replacement text.  Stop on a non-escaped newline.
    let mut text = Vec::new();
    'text_content: loop {
        if escaped_newline {
            match lines.next_line()? {
                None => {
                    break 'text_content;
                }
                Some(line_bytes) => {
                    *line = ScriptCharProvider::new(line_bytes);
                }
            }
            escaped_newline = false;
        }

        // Non-escaped newline
        if line.eol() {
            text.push(b'\n');
            break 'text_content;
        }

        if line.current() == '\\' {
            line.advance();

            if line.eol() {
                escaped_newline = true;
                text.push(b'\n');
                continue 'text_content;
            }

            if let Some(decoded) = parse_char_escape(line) {
                push_escaped_char(&mut text, decoded, context.character_mode);
            } else {
                // Invalid escapes result in the escaped character.
                text.push(line.current_byte());
                line.advance();
            }
        } else {
            text.push(line.current_byte());
            line.advance();
        }
    }
    cmd.data = CommandData::Text(Rc::from(text));
    Ok(CommandHandling::Continue)
}

/// Compile commands that take text as an argument (POSIX syntax).
// Handles a, c, i; after the command and initial whitespace have been consumed.
// According to POSIX, these commands expect \ followed by text.
fn compile_text_command_posix(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    _context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    if line.eol() || line.current() != '\\' {
        return compilation_error(lines, line, "expected \\ after `a', `c' or `i'".to_string());
    }

    line.advance(); // Skip \.
    line.eat_spaces(); // Skip any whitespace at the end of \.
    if !line.eol() {
        return compilation_error(
            lines,
            line,
            format!(
                "extra characters after \\ at the end of `{}' command",
                cmd.code
            ),
        );
    }

    let mut text = Vec::new();
    while let Some(line) = lines.next_line()? {
        if line.ends_with(b"\\") {
            // Line ends with \ to escape \n; remove the trailing \.
            text.extend_from_slice(&line[..line.len() - 1]);
            text.push(b'\n');
        } else {
            text.extend_from_slice(&line);
            text.push(b'\n');
            break;
        }
    }

    if text.is_empty() {
        compilation_error(lines, line, "incomplete command")?;
    }

    cmd.data = CommandData::Text(Rc::from(text));
    Ok(CommandHandling::Continue)
}

// Handle v
fn compile_version_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    _cmd: &mut Command,
    _context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    // Claim version partify with GNU sed 4.9
    const GNU_MAJOR: u8 = 4;
    const GNU_MINOR: u8 = 9;
    const GNU_PATCH: u8 = 0;

    line.advance();
    line.eat_spaces(); // Skip any leading whitespace.

    let mut major = String::new();
    let mut minor = String::new();
    let mut patch = String::new();

    let mut ver_semantic = 0;

    // Like a label, the version ends at whitespace or `;`, so `v 4.2;p` runs `p`.
    while !line.eol() && !line.current().is_whitespace() && line.current() != ';' {
        if line.current() == '.' {
            ver_semantic += 1;
            line.advance();
        } else {
            match ver_semantic {
                0 => major.push(line.current()),
                1 => minor.push(line.current()),
                2 => patch.push(line.current()),
                _ => return compilation_error(lines, line, "invalid version of sed"),
            }
            line.advance();
        }
    }

    if major.is_empty() {
        major = GNU_MAJOR.to_string();
        minor = GNU_MINOR.to_string();
        patch = GNU_PATCH.to_string();
    }

    if minor.is_empty() {
        minor.push('0');
    }
    if patch.is_empty() {
        patch.push('0');
    }

    match major.parse::<u8>() {
        Ok(major_int) => match minor.parse::<u8>() {
            Ok(minor_int) => match patch.parse::<u8>() {
                Ok(patch_int) => {
                    // Version order, as GNU's strverscmp gives: 3.99 is older than 4.9.
                    if (major_int, minor_int, patch_int) <= (GNU_MAJOR, GNU_MINOR, GNU_PATCH) {
                        return Ok(CommandHandling::Continue);
                    }
                    compilation_error(lines, line, "expected newer version of sed")
                }
                Err(_) => compilation_error(lines, line, "invalid version of sed"),
            },
            Err(_) => compilation_error(lines, line, "invalid version of sed"),
        },
        Err(_) => compilation_error(lines, line, "invalid version of sed"),
    }
}

// Handles e
// With no argument, the command executes the pattern space as a shell
// command at runtime. With an argument, the rest of the line is the
// command to run, following the same escape and backslash-newline
// continuation rules as the GNU a/c/i text argument.
fn compile_execute_command(
    lines: &mut ScriptLineProvider,
    line: &mut ScriptCharProvider,
    cmd: &mut Command,
    context: &mut ProcessingContext,
) -> UResult<CommandHandling> {
    if context.posix || context.sandbox {
        return compilation_error(
            lines,
            line,
            "the 'e' command is not allowed with --posix or --sandbox",
        );
    }
    if context.no_exec {
        return compilation_error(lines, line, ERR_NO_EXEC);
    }

    line.advance(); // Skip the command character.
    line.eat_spaces(); // Skip any leading whitespace.

    if line.eol() {
        // No argument: execute the pattern space itself at runtime.
        cmd.data = CommandData::None;
        return Ok(CommandHandling::Continue);
    }

    // True after a \ at the end of a line
    let mut escaped_newline = false;

    // Skip optional \
    if line.current() == '\\' {
        line.advance();
        escaped_newline = line.eol();
    }

    // Gather the command text. Stop on a non-escaped newline. Unlike most
    // other commands, ';' does not terminate the argument. The rest of the
    // (possibly continued) line is consumed unconditionally.
    let mut text = Vec::new();
    // True once a continuation line has actually been pulled in. A dangling
    // leading backslash with no line to continue into is treated as no
    // argument at all, matching GNU sed. However once a continuation succeeds,
    // even into an empty line, we're committed to producing a (possibly empty)
    // Text argument from then on.
    let mut continued = false;
    'text_content: loop {
        if escaped_newline {
            match lines.next_line()? {
                None => {
                    break 'text_content;
                }
                Some(line_bytes) => {
                    *line = ScriptCharProvider::new(line_bytes);
                    continued = true;
                }
            }
            escaped_newline = false;
        }

        // Non-escaped newline
        if line.eol() {
            break 'text_content;
        }

        if line.current() == '\\' {
            line.advance();

            if line.eol() {
                escaped_newline = true;
                text.push(b'\n');
                continue 'text_content;
            }

            if let Some(decoded) = parse_char_escape(line) {
                push_escaped_char(&mut text, decoded, context.character_mode);
            } else {
                // Invalid escapes result in the escaped character.
                text.push(line.current_byte());
                line.advance();
            }
        } else {
            text.push(line.current_byte());
            line.advance();
        }
    }

    cmd.data = if text.is_empty() && !continued {
        // A dangling leading backslash with nothing left to continue into.
        // Treat this the same as no argument at all.
        CommandData::None
    } else {
        CommandData::Text(Rc::from(text))
    };
    Ok(CommandHandling::Continue)
}

// Return the specification for the command letter at the current line position
// checking for diverse errors.
fn get_verified_cmd_spec(
    lines: &ScriptLineProvider,
    line: &ScriptCharProvider,
    n_addr: usize,
    posix: bool,
) -> UResult<CommandSpec> {
    if line.eol() {
        return compilation_error(lines, line, "command expected");
    }

    let ch = line.current();
    let cmd_spec = get_cmd_spec(lines, line, ch, posix)?;

    if n_addr > cmd_spec.n_addr {
        return compilation_error(
            lines,
            line,
            format!(
                "command {} expects up to {} address(es), found {}",
                ch, cmd_spec.n_addr, n_addr
            ),
        );
    }

    Ok(cmd_spec)
}

// Look up a command addresses and handler by its command code.
fn get_cmd_spec(
    lines: &ScriptLineProvider,
    line: &ScriptCharProvider,
    cmd_code: char,
    posix: bool,
) -> UResult<CommandSpec> {
    match cmd_code {
        '!' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_negation_command,
        }),
        '=' => Ok(CommandSpec {
            n_addr: if posix { 1 } else { 2 },
            handler: compile_empty_command,
        }),
        ':' => Ok(CommandSpec {
            n_addr: 0,
            handler: compile_label_command,
        }),
        '{' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_block_command,
        }),
        '}' => Ok(CommandSpec {
            n_addr: 0,
            handler: compile_end_group_command,
        }),
        'a' | 'i' => Ok(CommandSpec {
            n_addr: if posix { 1 } else { 2 },
            handler: compile_text_command,
        }),
        'b' | 't' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_label_command,
        }),
        'c' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_text_command,
        }),
        'd' | 'D' | 'g' | 'G' | 'h' | 'H' | 'n' | 'N' | 'p' | 'P' | 'x' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_empty_command,
        }),
        'z' if !posix => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_empty_command,
        }),
        'l' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_number_command,
        }),
        'q' => Ok(CommandSpec {
            n_addr: if posix { 1 } else { 2 },
            handler: compile_number_command,
        }),
        // Q is a GNU extension
        'Q' => Ok(CommandSpec {
            n_addr: 1,
            handler: compile_number_command,
        }),
        // e is a GNU extension
        'e' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_execute_command,
        }),
        'F' if !posix => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_empty_command,
        }),
        'r' => Ok(CommandSpec {
            n_addr: if posix { 1 } else { 2 },
            handler: compile_read_file_command,
        }),
        'R' if !posix => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_read_line_command,
        }),
        's' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_subst_command,
        }),
        'T' if !posix => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_label_command,
        }),
        'W' if !posix => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_write_file_command,
        }),
        'w' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_write_file_command,
        }),
        'y' => Ok(CommandSpec {
            n_addr: 2,
            handler: compile_trans_command,
        }),
        'v' if !posix => Ok(CommandSpec {
            n_addr: 0,
            handler: compile_version_command,
        }),
        _ => compilation_error(lines, line, format!("unknown command: `{cmd_code}'")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sed::fast_io::IOChunk;
    // Return an empty line provider and a char provider for the specified str.
    fn make_providers(input: &str) -> (ScriptLineProvider, ScriptCharProvider) {
        let lines = ScriptLineProvider::new(vec![]); // Empty for tests
        let line = ScriptCharProvider::new(input);
        (lines, line)
    }

    fn make_line_provider(lines: &[&str]) -> ScriptLineProvider {
        let input = lines
            .iter()
            .map(|s| ScriptValue::StringVal((*s).as_bytes().to_vec()))
            .collect();
        ScriptLineProvider::new(input)
    }

    fn make_char_provider(input: &str) -> ScriptCharProvider {
        ScriptCharProvider::new(input)
    }

    /// Return a default ProcessingContext for use in tests.
    pub fn ctx() -> ProcessingContext {
        ProcessingContext::default()
    }

    // get_cmd_spec
    #[test]
    fn test_lookup_empty_command() {
        let (lines, line) = make_providers("123abc");
        let cmd = get_cmd_spec(&lines, &line, 'd', false).unwrap();
        assert_eq!(cmd.n_addr, 2);
    }

    #[test]
    fn test_lookup_text_command() {
        let (lines, line) = make_providers("123abc");
        let cmd = get_cmd_spec(&lines, &line, 'a', false).unwrap();
        assert_eq!(cmd.n_addr, 2);
    }

    #[test]
    fn test_lookup_nonselect_command() {
        let (lines, line) = make_providers("123abc");
        let cmd = get_cmd_spec(&lines, &line, '!', false).unwrap();
        assert_eq!(cmd.n_addr, 2);
    }

    #[test]
    fn test_lookup_endgroup_command() {
        let (lines, line) = make_providers("123abc");
        let cmd = get_cmd_spec(&lines, &line, '}', false).unwrap();
        assert_eq!(cmd.n_addr, 0);
    }

    #[test]
    fn test_lookup_invalid_command() {
        let (lines, line) = make_providers("123abc");
        let result = get_cmd_spec(&lines, &line, 'Z', false);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_command_ending_rejects_extra_characters() {
        let (lines, mut chars) = make_providers("extra");
        let mut cmd = Command {
            code: 'p',
            ..Default::default()
        };

        let err = parse_command_ending(&lines, &mut chars, &mut cmd).unwrap_err();
        assert!(
            err.to_string()
                .contains("extra characters at the end of the p command")
        );
    }

    #[test]
    fn test_lookup_branch_commands() {
        // b, t, and T all share compile_label_command and accept 2 addresses.
        for code in ['b', 't', 'T'] {
            let (lines, line) = make_providers("123abc");
            let cmd = get_cmd_spec(&lines, &line, code, false).unwrap();
            assert_eq!(cmd.n_addr, 2, "command `{code}` should accept 2 addresses");
        }
    }

    // Utility to create a ScriptCharProvider from a &str
    fn char_provider_from(s: &str) -> ScriptCharProvider {
        ScriptCharProvider::new(s)
    }

    // compilation_error
    #[test]
    fn test_compilation_error_message_format() {
        let lines = ScriptLineProvider::with_active_state("test.sed", 42);
        let mut line = char_provider_from("whatever");
        line.advance(); // move to position 1
        line.advance(); // move to position 2
        line.advance(); // move to position 3
        line.advance(); // now at position 4

        let msg = "unexpected token";
        let result: UResult<()> = compilation_error(&lines, &line, msg);

        assert!(result.is_err());

        let err = result.unwrap_err();
        let msg = err.to_string();

        assert!(msg.contains("test.sed:42:5: error: unexpected token"));
    }

    #[test]
    fn test_compilation_error_with_format_message() {
        let lines = ScriptLineProvider::with_active_state("input.txt", 3);
        let line = char_provider_from("x");
        // We're at position 0

        let result: UResult<()> =
            compilation_error(&lines, &line, format!("invalid command '{}'", 'x'));

        assert!(result.is_err());

        let err = result.unwrap_err();
        let msg = err.to_string();

        assert_eq!(msg, "input.txt:3:1: error: invalid command 'x'");
    }

    // get_verified_cmd_spec
    #[test]
    fn test_missing_command_character() {
        let lines = ScriptLineProvider::with_active_state("test.sed", 1);
        let line = char_provider_from("");
        let result = get_verified_cmd_spec(&lines, &line, 0, ctx().posix);

        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(msg.contains("test.sed:1:0: error: command expected"));
    }

    #[test]
    fn test_invalid_command_character() {
        let lines = ScriptLineProvider::with_active_state("script.sed", 2);
        let line = char_provider_from("@");
        let result = get_verified_cmd_spec(&lines, &line, 0, ctx().posix);

        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(msg.contains("script.sed:2:1: error: unknown command: `@'"));
    }

    #[test]
    fn test_too_many_addresses() {
        let lines = ScriptLineProvider::with_active_state("input.sed", 3);
        let line = char_provider_from("q"); // q takes one address
        let result = get_verified_cmd_spec(&lines, &line, 2, true);

        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(
            msg.contains("input.sed:3:1: error: command q expects up to 1 address(es), found 2")
        );
    }

    #[test]
    fn test_valid_command_spec() {
        let lines = ScriptLineProvider::with_active_state("input.sed", 4);
        let line = char_provider_from("a"); // valid command
        let result = get_verified_cmd_spec(&lines, &line, 2, ctx().posix);
        assert!(result.is_ok());
        let spec = result.unwrap();
        assert_eq!(spec.n_addr, 2);
    }

    #[test]
    fn test_invalid_address_range_posix() {
        let lines = ScriptLineProvider::with_active_state("input.sed", 1);
        let line = char_provider_from("i"); // valid command
        let result = get_verified_cmd_spec(&lines, &line, 2, true);
        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(
            msg.contains("input.sed:1:1: error: command i expects up to 1 address(es), found 2")
        );
    }

    // parse_number
    #[test]
    fn test_parse_number_basic() {
        let (lines, mut chars) = make_providers("123abc");
        assert_eq!(parse_number(&lines, &mut chars, true).unwrap(), Some(123));
        assert_eq!(chars.current(), 'a'); // Should stop at first non-digit
    }

    #[test]
    fn test_parse_optional_number_missing() {
        let (lines, mut chars) = make_providers(" ;");
        assert_eq!(parse_number(&lines, &mut chars, false).unwrap(), None);
    }

    #[test]
    fn test_parse_number_invalid() {
        let (lines, mut chars) = make_providers("537654897563495734653453434534534534545");
        let err = parse_number(&lines, &mut chars, true).unwrap_err();
        assert!(err.to_string().contains("invalid number"));
    }

    #[test]
    fn test_parse_required_number_missing() {
        let (lines, mut chars) = make_providers("");
        let err = parse_number(&lines, &mut chars, true).unwrap_err();
        assert!(err.to_string().contains("number expected"));
    }

    // compile_re
    fn dummy_providers() -> (ScriptLineProvider, ScriptCharProvider) {
        make_providers("dummy input")
    }

    #[test]
    fn test_compile_re_basic() {
        let (lines, chars) = dummy_providers();
        let regex = compile_regex(&lines, &chars, "abc", &ctx(), false, false)
            .unwrap()
            .expect("regex should be present");
        assert!(regex.is_match(&mut IOChunk::new_from_str("abc")).unwrap());
        assert!(!regex.is_match(&mut IOChunk::new_from_str("ABC")).unwrap());
    }

    #[test]
    fn test_compile_re_extended() {
        let (lines, chars) = make_providers("acaa\nbbb\nccc");
        let mut ctx = ctx();
        ctx.regex_extended = true;
        let regex = compile_regex(&lines, &chars, "cc{0,}", &ctx, false, false)
            .unwrap()
            .expect("regex should be present");
        assert!(
            regex
                .is_match(&mut IOChunk::new_from_str("acaa\nccc"))
                .unwrap()
        );
    }

    #[test]
    fn test_compile_re_case_insensitive() {
        let (lines, chars) = dummy_providers();
        let regex = compile_regex(&lines, &chars, "abc", &ctx(), true, false)
            .unwrap()
            .expect("regex should be present");
        assert!(regex.is_match(&mut IOChunk::new_from_str("abc")).unwrap());
        assert!(regex.is_match(&mut IOChunk::new_from_str("ABC")).unwrap());
        assert!(regex.is_match(&mut IOChunk::new_from_str("AbC")).unwrap());
    }

    #[test]
    fn test_compile_re_invalid() {
        let (lines, chars) = dummy_providers();
        let result = compile_regex(&lines, &chars, "a[d", &ctx(), false, false);
        assert!(result.is_err()); // Should fail due to open bracketed expression
    }

    #[test]
    fn test_compile_re_multiline_start() {
        let (lines, chars) = dummy_providers();
        let regex = compile_regex(&lines, &chars, "^bar", &ctx(), false, true)
            .unwrap()
            .expect("regex should be present");
        assert!(
            regex
                .is_match(&mut IOChunk::new_from_str("foo\nbar"))
                .unwrap()
        );
    }

    #[test]
    fn test_compile_re_multiline_end() {
        let (lines, chars) = dummy_providers();
        let regex = compile_regex(&lines, &chars, "foo$", &ctx(), false, true)
            .unwrap()
            .expect("regex should be present");
        assert!(
            regex
                .is_match(&mut IOChunk::new_from_str("foo\nbar"))
                .unwrap()
        );
    }

    // compile_address
    #[test]
    fn test_compile_addr_line_number() {
        let (lines, mut chars) = make_providers("42");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();
        assert!(matches!(addr, Address::Line(42)));
    }

    #[test]
    fn test_compile_addr_relative_line() {
        let (lines, mut chars) = make_providers("+7");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();
        assert!(matches!(addr, Address::RelLine(7)));
    }

    #[test]
    fn test_compile_addr_last_line() {
        let (lines, mut chars) = make_providers("$");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();
        assert!(matches!(addr, Address::Last));
    }

    #[test]
    fn test_compile_addr_regex() {
        let (lines, mut chars) = make_providers("/hello/");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();

        let Address::Re(Some(re)) = addr else {
            panic!("expected Address::Re(Some(_))");
        };

        assert!(re.is_match(&mut IOChunk::new_from_str("hello")).unwrap());
    }

    #[test]
    fn test_compile_addr_regex_backref_match() {
        let (lines, mut chars) = make_providers(r"/he\(.\)\1o/");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();

        match addr {
            Address::Re(Some(re)) => {
                assert!(re.is_match(&mut IOChunk::new_from_str("hello")).unwrap());
            }
            _ => panic!("expected Address::Re(Some(_))"),
        }
    }

    #[test]
    fn test_compile_addr_regex_backref_no_match() {
        let (lines, mut chars) = make_providers(r"/he\(.\)\1o/");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();

        match addr {
            Address::Re(Some(re)) => {
                assert!(!re.is_match(&mut IOChunk::new_from_str("helio")).unwrap());
            }
            _ => panic!("expected Address::Re(Some(_))"),
        }
    }

    #[test]
    fn test_compile_addr_regex_other_delimiter() {
        let (lines, mut chars) = make_providers("\\#hello#");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();

        match addr {
            Address::Re(Some(re)) => {
                assert!(re.is_match(&mut IOChunk::new_from_str("hello")).unwrap());
            }
            _ => panic!("expected Address::Re(Some(_))"),
        }
    }

    #[test]
    fn test_compile_addr_regex_with_modifier() {
        let (lines, mut chars) = make_providers("/hello/I");
        let addr = compile_address(&lines, &mut chars, &ctx()).unwrap();

        match addr {
            Address::Re(Some(re)) => {
                // Case-insensitive
                assert!(re.is_match(&mut IOChunk::new_from_str("HELLO")).unwrap());
            }
            _ => panic!("expected Address::Re(Some(_))"),
        }
    }

    // compile_address_range
    #[test]
    fn test_compile_single_line_address() {
        let (lines, mut chars) = make_providers("42");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 1);
        assert!(matches!(cmd.borrow().addr1, Some(Address::Line(42))));
    }

    #[test]
    fn test_compile_relative_address_range() {
        let (lines, mut chars) = make_providers("2,+3");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 2);

        assert!(matches!(cmd.borrow().addr1, Some(Address::Line(2))));
        assert!(matches!(cmd.borrow().addr2, Some(Address::RelLine(3))));
    }

    #[test]
    fn test_compile_step_match_address() {
        let (lines, mut chars) = make_providers("0~2");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 2);
        assert!(matches!(cmd.borrow().addr1, Some(Address::Line(0))));
        assert!(matches!(cmd.borrow().addr2, Some(Address::StepMatch(2))));
    }

    #[test]
    fn test_compile_step_end_address() {
        let (lines, mut chars) = make_providers("1,~10");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 2);
        assert!(matches!(cmd.borrow().addr1, Some(Address::Line(1))));
        assert!(matches!(cmd.borrow().addr2, Some(Address::StepEnd(10))));
    }

    #[test]
    fn test_compile_step_re_address_rejected() {
        let (lines, mut chars) = make_providers("1~/x/");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let err = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap_err();

        assert!(
            err.to_string()
                .contains("~step can only be specified through numeric values")
        );
    }

    #[test]
    fn test_compile_last_address() {
        let (lines, mut chars) = make_providers("$");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 1);
        assert!(matches!(cmd.borrow().addr1, Some(Address::Last)));
    }

    #[test]
    fn test_compile_absolute_address_range() {
        let (lines, mut chars) = make_providers("5,10");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 2);
        assert!(matches!(cmd.borrow().addr1, Some(Address::Line(5))));
        assert!(matches!(cmd.borrow().addr2, Some(Address::Line(10))));
    }

    #[test]
    fn test_compile_regex_address() {
        let (lines, mut chars) = make_providers("/foo/");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 1);

        match cmd.borrow().addr1.as_ref().unwrap() {
            Address::Re(Some(re)) => {
                assert!(re.is_match(&mut IOChunk::new_from_str("foo")).unwrap());
                assert!(!re.is_match(&mut IOChunk::new_from_str("bar")).unwrap());
            }
            _ => panic!("expected regex address"),
        }
    }

    #[test]
    fn test_compile_regex_address_range_other_delimiter() {
        let (lines, mut chars) = make_providers("\\#foo# , \\|bar|");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 2);

        match cmd.borrow().addr1.as_ref().unwrap() {
            Address::Re(Some(re)) => {
                assert!(re.is_match(&mut IOChunk::new_from_str("foo")).unwrap());
                assert!(!re.is_match(&mut IOChunk::new_from_str("bar")).unwrap());
            }
            _ => panic!("expected regex address"),
        }

        match cmd.borrow().addr2.as_ref().unwrap() {
            Address::Re(Some(re)) => {
                assert!(re.is_match(&mut IOChunk::new_from_str("bar")).unwrap());
                assert!(!re.is_match(&mut IOChunk::new_from_str("foo")).unwrap());
            }
            _ => panic!("expected regex address"),
        }
    }

    #[test]
    fn test_compile_regex_with_modifier() {
        let (lines, mut chars) = make_providers("/foo/I");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

        assert_eq!(n_addr, 1);

        match cmd.borrow().addr1.as_ref().unwrap() {
            Address::Re(Some(re)) => {
                assert!(re.is_match(&mut IOChunk::new_from_str("FOO")).unwrap());
                assert!(re.is_match(&mut IOChunk::new_from_str("foo")).unwrap());
            }
            _ => panic!("expected regex address"),
        }
    }

    #[test]
    fn test_compile_address_range_error_propagation() {
        let (lines, mut chars) = make_providers("1,/abc");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let result = compile_address_range(&lines, &mut chars, &mut cmd, &ctx());

        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(msg.contains("unterminated address regex"));
    }

    // compile_sequence
    fn empty_line() -> ScriptCharProvider {
        ScriptCharProvider::new("")
    }

    #[test]
    fn test_zero_addr_r_accepted() {
        for input in ["0r", "0  r"] {
            let (lines, mut chars) = make_providers(input);
            let mut cmd = Rc::new(RefCell::new(Command::default()));
            let n_addr = compile_address_range(&lines, &mut chars, &mut cmd, &ctx()).unwrap();

            assert_eq!(n_addr, 1);
            assert!(matches!(cmd.borrow().addr1, Some(Address::Line(0))));
            assert_eq!(chars.current(), 'r');
        }
    }

    // Zero-address with no commands
    #[test]
    fn test_zero_addr_no_commands() {
        let (lines, mut chars) = make_providers("0");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let result = compile_address_range(&lines, &mut chars, &mut cmd, &ctx());

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains(ERR_ADDRESS_0_USAGE)
        );
    }

    // Zero-address with a command other than 'r' must still be rejected.
    #[test]
    fn test_zero_addr_non_r_rejected() {
        let (lines, mut chars) = make_providers("0p");
        let mut cmd = Rc::new(RefCell::new(Command::default()));
        let result = compile_address_range(&lines, &mut chars, &mut cmd, &ctx());

        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains(ERR_ADDRESS_0_USAGE)
        );
    }

    #[test]
    fn test_compile_sequence_empty_input() {
        let mut provider = make_line_provider(&[]);
        let mut opts = ctx();

        let result = compile_sequence(&mut provider, &mut empty_line(), &mut opts).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn test_compile_sequence_comment_only() {
        let mut provider = make_line_provider(&["# comment", "   ", ";;"]);
        let mut opts = ctx();

        let result = compile_sequence(&mut provider, &mut empty_line(), &mut opts).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn test_compile_sequence_single_command() {
        let mut provider = make_line_provider(&["42q"]);
        let mut opts = ctx();

        let result = compile_sequence(&mut provider, &mut empty_line(), &mut opts).unwrap();
        let binding = result.unwrap();
        let cmd = binding.borrow();

        assert_eq!(cmd.code, 'q');
        assert!(!cmd.non_select);

        assert!(matches!(cmd.addr1, Some(Address::Line(42))));
        assert!(cmd.next.is_none());
    }

    #[test]
    fn test_compile_sequence_non_selected_single_command() {
        let mut provider = make_line_provider(&["42!p"]);
        let mut opts = ctx();

        let result = compile_sequence(&mut provider, &mut empty_line(), &mut opts).unwrap();
        let binding = result.unwrap();
        let cmd = binding.borrow();

        assert_eq!(cmd.code, 'p');
        assert!(cmd.non_select);

        assert!(matches!(cmd.addr1, Some(Address::Line(42))));
        assert!(cmd.next.is_none());
    }

    #[test]
    fn test_compile_sequence_multiple_lines() {
        let mut provider = make_line_provider(&["1q", "2d"]);
        let mut opts = ctx();

        let result = compile_sequence(&mut provider, &mut empty_line(), &mut opts).unwrap();
        let binding = result.unwrap();
        let first = binding.borrow();

        assert_eq!(first.code, 'q');
        let binding = first.next.clone().unwrap();
        let second = binding.borrow();
        assert_eq!(second.code, 'd');
        assert!(second.next.is_none());
    }

    #[test]
    fn test_compile_sequence_single_line_multiple_commands() {
        let mut provider = make_line_provider(&["1q;2d"]);
        let mut opts = ctx();

        let result = compile_sequence(&mut provider, &mut empty_line(), &mut opts).unwrap();
        let binding = result.unwrap();
        let first = binding.borrow();

        assert_eq!(first.code, 'q');
        let binding = first.next.clone().unwrap();
        let second = binding.borrow();
        assert_eq!(second.code, 'd');
        assert!(second.next.is_none());
    }

    // compile
    #[test]
    fn test_compile_single_command() {
        let scripts = vec![ScriptValue::StringVal(b"1q".to_vec())];
        let mut opts = ProcessingContext::default();

        let result = compile(scripts, &mut opts).unwrap();
        let binding = result.unwrap();
        let cmd = binding.borrow();

        assert_eq!(cmd.code, 'q');

        assert!(matches!(cmd.addr1, Some(Address::Line(1))));

        assert_eq!(cmd.location.line_number, 1);
        assert_eq!(cmd.location.column_number, 1);
        assert_eq!(cmd.location.input_name.as_ref(), "<script argument 1>");

        assert!(cmd.next.is_none());
    }

    #[test]
    fn test_compile_two_commands() {
        let scripts = vec![ScriptValue::StringVal(b"l;q".to_vec())];
        let mut opts = ProcessingContext::default();

        let result = compile(scripts, &mut opts).unwrap();
        let binding = result.unwrap();
        let cmd = binding.borrow();

        assert_eq!(cmd.code, 'l');
        assert_eq!(cmd.location.line_number, 1);
        assert_eq!(cmd.location.column_number, 1);
        assert_eq!(cmd.location.input_name.as_ref(), "<script argument 1>");

        let binding2 = cmd.next.clone().unwrap();
        let cmd2 = binding2.borrow();
        assert_eq!(cmd2.code, 'q');
        assert_eq!(cmd2.location.line_number, 1);
        assert_eq!(cmd2.location.column_number, 3);
        assert_eq!(cmd2.location.input_name.as_ref(), "<script argument 1>");

        assert!(cmd2.next.is_none());
    }

    // compile_replacement

    /// Compile a regular expression replacement string in UTF-8 mode.
    fn compile_replacement_utf8(
        lines: &mut ScriptLineProvider,
        line: &mut ScriptCharProvider,
    ) -> UResult<ReplacementTemplate> {
        compile_replacement(lines, line, CharacterMode::Utf8)
    }

    #[test]
    fn test_compile_replacement_literal() {
        let (mut lines, mut chars) = make_providers("/hello/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"hello"));
    }

    #[test]
    fn test_compile_replacement_escaped_delimiter() {
        let (mut lines, mut chars) = make_providers(r"/hell\/o/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"hell/o"));
    }

    #[test]
    fn test_compile_replacement_backrefs_and_literal() {
        let (mut lines, mut chars) = make_providers("/prefix \\1 and \\2/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 4);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"prefix "));
        assert!(matches!(&template.parts[1], ReplacementPart::Group(1)));
        assert!(matches!(&template.parts[2], ReplacementPart::Literal(s) if s == b" and "));
        assert!(matches!(&template.parts[3], ReplacementPart::Group(2)));
    }

    #[test]
    fn test_compile_replacement_whole_match() {
        let (mut lines, mut chars) = make_providers("/The match was: &/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 2);
        assert!(
            matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"The match was: ")
        );
        assert!(matches!(&template.parts[1], ReplacementPart::WholeMatch));
    }

    #[test]
    fn test_compile_replacement_whole_match_synonym() {
        let (mut lines, mut chars) = make_providers(r"/The match was: \0/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 2);
        assert!(
            matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"The match was: ")
        );
        assert!(matches!(&template.parts[1], ReplacementPart::WholeMatch));
    }

    #[test]
    fn test_compile_replacement_ampersand() {
        let (mut lines, mut chars) = make_providers("/Simon \\& Garfunkel/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(
            matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"Simon & Garfunkel")
        );
    }

    #[test]
    fn test_compile_replacement_escape_sequences() {
        let (mut lines, mut chars) = make_providers("/line\\nnewline\\tend/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(
            &template.parts[0],
            ReplacementPart::Literal(s) if s == b"line\nnewline\tend"
        ));
    }

    #[test]
    fn test_compile_replacement_escape_byte_mode() {
        let (mut lines, mut chars) = make_providers("/\\xE9/");
        let template = compile_replacement(&mut lines, &mut chars, CharacterMode::Byte).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"\xE9"));
    }

    #[test]
    fn test_compile_replacement_escape_utf8_mode() {
        // GNU inserts the literal byte a `\xHH` escape produces, never a UTF-8 encoding of it,
        // regardless of character mode: same expectation as `..._byte_mode` above.
        let (mut lines, mut chars) = make_providers("/\\xE9/");
        let template = compile_replacement(&mut lines, &mut chars, CharacterMode::Utf8).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"\xE9"));
    }

    #[test]
    fn test_compile_replacement_line_continuation() {
        let script = vec![
            ScriptValue::StringVal(b"/first line\\".to_vec()),
            ScriptValue::StringVal(b" continued/".to_vec()),
        ];
        let mut provider = ScriptLineProvider::new(script);
        let first_line = provider.next_line().unwrap().unwrap();
        let mut chars = ScriptCharProvider::new(first_line);

        let template = compile_replacement_utf8(&mut provider, &mut chars).unwrap();
        assert_eq!(template.parts.len(), 1);
        assert!(matches!(
            &template.parts[0],
            ReplacementPart::Literal(s) if s == b"first line\n continued"
        ));
    }

    #[test]
    fn test_compile_replacement_preserves_invalid_utf8_script_byte() {
        let mut chars = ScriptCharProvider::new(b"/\xC2/");
        let mut lines = ScriptLineProvider::new(vec![]);

        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == b"\xC2"));
    }

    #[test]
    fn test_compile_replacement_preserves_unknown_escape() {
        let (mut lines, mut chars) = make_providers(r"/a\q/");
        let template = compile_replacement_utf8(&mut lines, &mut chars).unwrap();

        assert_eq!(template.parts.len(), 1);
        assert!(matches!(&template.parts[0], ReplacementPart::Literal(s) if s == br"a\q"));
    }

    #[test]
    fn test_compile_replacement_eof_after_backslash() {
        let (mut lines, mut chars) = make_providers(r"/abc\");
        let err = compile_replacement_utf8(&mut lines, &mut chars).unwrap_err();

        assert!(err.to_string().contains("unterminated `s' command"));
    }

    #[test]
    fn test_compile_replacement_unescaped_newline() {
        let (mut lines, mut chars) = make_providers("/abc\n/");
        let err = compile_replacement_utf8(&mut lines, &mut chars).unwrap_err();

        assert!(
            err.to_string()
                .contains("unescaped newline inside substitute replacement")
        );
    }

    #[test]
    fn test_compile_replacement_unterminated() {
        let (mut lines, mut chars) = make_providers("/abc");
        let err = compile_replacement_utf8(&mut lines, &mut chars).unwrap_err();

        assert!(err.to_string().contains("unterminated `s' command"));
    }

    // compile_subst_flags
    #[test]
    fn test_compile_subst_flag_g() {
        let (lines, mut chars) = make_providers("g");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert_eq!(subst.occurrence, 0); // 'g' means all occurrences
    }

    #[test]
    fn test_compile_subst_flag_p() {
        let (lines, mut chars) = make_providers("p");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert!(subst.print_flag);
    }

    #[test]
    fn test_compile_subst_flag_uppercase_i() {
        let (lines, mut chars) = make_providers("I");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert!(subst.ignore_case);
    }

    #[test]
    fn test_compile_subst_flag_i_lowercase() {
        let (lines, mut chars) = make_providers("i");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert!(subst.ignore_case);
    }

    #[test]
    fn test_compile_subst_flag_uppercase_m() {
        let (lines, mut chars) = make_providers("M");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert!(subst.multiline);
    }

    #[test]
    fn test_compile_subst_flag_m_lowercase() {
        let (lines, mut chars) = make_providers("m");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert!(subst.multiline);
    }

    #[test]
    fn test_compile_subst_flag_number() {
        let (lines, mut chars) = make_providers("3");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert_eq!(subst.occurrence, 3);
    }

    #[test]
    fn test_compile_subst_flag_g_and_number_combine() {
        // GNU: replace the Nth match and every later one, in either order.
        for flags in ["g3", "3g"] {
            let (lines, mut chars) = make_providers(flags);
            let mut subst = Substitution::default();
            compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
            assert_eq!((subst.occurrence, subst.global), (3, true));
        }
        let (lines, mut chars) = make_providers("1g");
        let mut subst = Substitution::default();
        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert_eq!((subst.occurrence, subst.global), (0, false));
    }

    #[test]
    fn test_compile_subst_flag_repeated_g_or_number_fails() {
        for flags in ["gg", "3g4"] {
            let (lines, mut chars) = make_providers(flags);
            let mut subst = Substitution::default();
            let err =
                compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap_err();
            assert!(
                err.to_string()
                    .contains("multiple `g' options to `s' command")
            );
        }
    }

    #[test]
    fn test_compile_subst_flag_w_missing_filename() {
        let (lines, mut chars) = make_providers("w ");
        let mut subst = Substitution::default();

        let err = compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap_err();
        assert!(
            err.to_string()
                .contains("missing filename in r/R/w/W commands")
        );
    }

    #[test]
    fn test_compile_subst_flag_w_with_filename() {
        let tmp_dir = tempfile::tempdir().expect("failed to create tmp folder");
        let out = tmp_dir.path().join("out.txt");
        let (lines, mut chars) = make_providers(&format!("w {}", out.display()));
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert_eq!(
            subst.write_file.as_ref().map(|w| w.borrow().path.clone()),
            Some(out)
        );
    }

    #[test]
    fn test_compile_subst_flag_w_rejected_under_sandbox() {
        let (lines, mut chars) = make_providers("w out.txt");
        let mut subst = Substitution::default();

        let err = compile_subst_flags(&lines, &mut chars, &mut subst, false, true).unwrap_err();
        assert!(err.to_string().contains(ERR_SANDBOX));
    }

    #[test]
    fn test_compile_subst_flag_e() {
        let (lines, mut chars) = make_providers("e");
        let mut subst = Substitution::default();

        compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap();
        assert!(subst.execute);
    }

    #[test]
    fn test_compile_subst_flag_e_rejected_under_posix() {
        let (lines, mut chars) = make_providers("e");
        let mut subst = Substitution::default();

        let err = compile_subst_flags(&lines, &mut chars, &mut subst, true, false).unwrap_err();
        assert!(
            err.to_string()
                .contains("not allowed with --posix or --sandbox")
        );
    }

    #[test]
    fn test_compile_subst_flag_e_rejected_under_sandbox() {
        let (lines, mut chars) = make_providers("e");
        let mut subst = Substitution::default();

        let err = compile_subst_flags(&lines, &mut chars, &mut subst, false, true).unwrap_err();
        assert!(
            err.to_string()
                .contains("not allowed with --posix or --sandbox")
        );
    }

    #[test]
    fn test_compile_subst_flag_invalid_flag() {
        let (lines, mut chars) = make_providers("z");
        let mut subst = Substitution::default();

        let err = compile_subst_flags(&lines, &mut chars, &mut subst, false, false).unwrap_err();
        assert!(err.to_string().contains("unknown option to `s'"));
    }

    // compile_subst_command
    #[test]
    fn test_compile_subst_invalid_delimiter_backslash() {
        let (mut lines, mut chars) = make_providers("s\\foo\\bar\\");
        let mut cmd = Command::default();
        let mut context = ctx();

        let err =
            compile_subst_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(
            err.to_string()
                .contains("substitute pattern cannot be delimited")
        );
    }

    #[test]
    fn test_compile_subst_extra_characters_at_end() {
        let (mut lines, mut chars) = make_providers("s/foo/bar/x");
        let mut cmd = Command::default();
        let mut context = ctx();

        let err =
            compile_subst_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(err.to_string().contains("unknown option to `s'"));
    }

    #[test]
    fn test_compile_subst_semicolon_indicates_continue() {
        let (mut lines, mut chars) = make_providers("s/foo/bar/;");
        let mut cmd = Command::default();
        let mut context = ctx();

        compile_subst_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();

        if let CommandData::Substitution(subst) = &cmd.data {
            assert_eq!(subst.replacement.parts.len(), 1);
        } else {
            panic!("Expected CommandData::Substitution");
        }
    }

    #[test]
    fn test_compile_subst_sets_command_data() {
        let (mut lines, mut chars) = make_providers("s/foo/bar/");
        let mut cmd = Command::default();
        let mut context = ctx();

        compile_subst_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Substitution(subst) => {
                assert_eq!(subst.replacement.parts.len(), 1);
                assert!(
                    matches!(&subst.replacement.parts[0], ReplacementPart::Literal(s) if s == b"bar")
                );
            }
            _ => panic!("Expected CommandData::Substitution"),
        }
    }

    #[test]
    fn test_compile_subst_invalid_group_reference() {
        let (mut lines, mut chars) = make_providers(r"s/f(o)o/\2/");
        let mut cmd = Command::default();
        let mut context = ctx();

        let err =
            compile_subst_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(err.to_string().contains("invalid reference \\2"));
    }

    #[test]
    fn test_compile_subst_empty_re_rejects_modifiers() {
        let (mut lines, mut chars) = make_providers("s//x/I");
        let mut cmd = Command::default();
        let mut context = ctx();

        let err =
            compile_subst_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(
            err.to_string()
                .contains("cannot specify modifiers on an empty regular expression")
        );
    }

    #[test]
    fn test_compile_trans_command_sets_command_data() {
        let (mut lines, mut chars) = make_providers("y/ab/xy/");
        let mut cmd = Command::default();
        let mut context = ProcessingContext {
            character_mode: CharacterMode::Byte,
            ..ctx()
        };

        compile_trans_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Transliteration(trans) => {
                assert_eq!(trans.lookup_byte(b'a'), b'x');
                assert_eq!(trans.lookup_byte(b'b'), b'y');
                assert_eq!(trans.lookup_byte(b'c'), b'c');
            }
            _ => panic!("Expected CommandData::Transliteration"),
        }
    }

    // bre_to_ere
    fn bre_to_ere_string(pattern: &str) -> String {
        String::from_utf8(bre_to_ere(pattern.as_bytes())).unwrap()
    }

    #[test]
    fn test_bre_group_translation() {
        assert_eq!(bre_to_ere_string(r"\(a\?b\+c\|\)"), "(a?b+c|)");
        assert_eq!(bre_to_ere_string(r"a\(b\)c"), "a(b)c");
    }

    #[test]
    fn test_bre_brace_quantifier_translation() {
        assert_eq!(bre_to_ere_string(r"\{1,4\}"), "{1,4}");
    }

    #[test]
    fn test_ere_metacharacters_escaped() {
        assert_eq!(bre_to_ere_string(r"a+b?c{1}|(d)"), r"a\+b\?c\{1\}\|\(d\)");
    }

    #[test]
    fn test_literal_backslashes_preserved() {
        assert_eq!(bre_to_ere_string(r"foo\\bar"), r"foo\\bar");
        assert_eq!(bre_to_ere_string(r"\."), r"\.");
    }

    #[test]
    fn test_character_classes_unchanged() {
        assert_eq!(bre_to_ere_string(r"[a-z]"), "[a-z]");
        assert_eq!(bre_to_ere_string(r"[^0-9]"), "[^0-9]");
    }

    #[test]
    fn test_anchors_and_dot_and_star() {
        assert_eq!(bre_to_ere_string(r"^a.*b$"), "^a.*b$");
    }

    #[test]
    fn test_trailing_backslash_is_preserved() {
        assert_eq!(bre_to_ere_string(r"abc\"), r"abc\");
    }

    #[test]
    fn test_caret_escaped_in_middle() {
        assert_eq!(bre_to_ere_string(r"^a^[^x]c"), r"^a\^[^x]c");
    }

    #[test]
    fn test_dollar_escaped_in_middle() {
        assert_eq!(bre_to_ere_string(r"a$c$"), r"a\$c$");
    }

    #[test]
    fn test_bre_back_reference() {
        assert_eq!(bre_to_ere_string(r"\(.\)\1\(.\)\2"), r"(.)(?:\1)(.)(?:\2)");
    }

    // patch_block_endings

    // Create a command with the specified code.
    fn command_with_code(code: char) -> Rc<RefCell<Command>> {
        Rc::new(RefCell::new(Command {
            code,
            ..Default::default()
        }))
    }

    // Link the vector of passed commands into a list, returning head.
    fn link_commands(cmds: Vec<Rc<RefCell<Command>>>) -> Option<Rc<RefCell<Command>>> {
        for i in 0..cmds.len().saturating_sub(1) {
            cmds[i].borrow_mut().next = Some(cmds[i + 1].clone());
        }
        cmds.first().cloned()
    }

    // Return the command codes along the passed linked list.
    fn collect_codes(mut head: Option<Rc<RefCell<Command>>>) -> Vec<char> {
        let mut result = Vec::new();
        while let Some(cmd) = head {
            let cmd_ref = cmd.borrow();
            result.push(cmd_ref.code);
            head = cmd_ref.next.clone();
        }
        result
    }

    #[test]
    fn test_flat_chain() {
        let a = command_with_code('a');
        let b = command_with_code('b');
        let head = link_commands(vec![a, b]);

        patch_block_endings(head.clone());

        assert_eq!(collect_codes(head), vec!['a', 'b']);
    }

    #[test]
    fn test_simple_block_relinks_tail() {
        // a ; { x ; y ; } b
        let a = command_with_code('a');
        let block = command_with_code('{');
        let x = command_with_code('x');
        let y = command_with_code('y');
        let b = command_with_code('b');

        let head = link_commands(vec![a.clone(), block.clone(), b]);
        let sub_head = link_commands(vec![x, y]);
        block.borrow_mut().data = CommandData::BranchTarget(sub_head.clone());

        patch_block_endings(head);

        // Expect x -> y -> b
        assert_eq!(collect_codes(sub_head), vec!['x', 'y', 'b']);
        // Expect a -> { -> b still valid
        assert_eq!(collect_codes(Some(a)), vec!['a', '{', 'b']);
    }

    #[test]
    fn test_empty_block_no_panic() {
        let a = command_with_code('a');
        a.borrow_mut().data = CommandData::BranchTarget(None);

        patch_block_endings(Some(a.clone()));

        assert_eq!(collect_codes(Some(a)), vec!['a']);
    }

    #[test]
    fn test_nested_blocks() {
        // a
        // {
        //   m
        //   {
        //     x
        //     y
        //   }
        //   n
        // }
        // b
        let a = command_with_code('a');
        let b = command_with_code('b');
        let x = command_with_code('x');
        let y = command_with_code('y');
        let m = command_with_code('m');
        let n = command_with_code('n');
        let outer_block = command_with_code('{');
        let inner_block = command_with_code('{');

        let head = link_commands(vec![a, outer_block.clone(), b]);
        let outer = link_commands(vec![m, inner_block.clone(), n]);
        let inner = link_commands(vec![x, y]);
        outer_block.borrow_mut().data = CommandData::BranchTarget(outer.clone());
        inner_block.borrow_mut().data = CommandData::BranchTarget(inner.clone());

        patch_block_endings(head.clone());

        assert_eq!(collect_codes(head), vec!['a', '{', 'b']);
        assert_eq!(collect_codes(inner), vec!['x', 'y', 'n', 'b']);
        assert_eq!(collect_codes(outer), vec!['m', '{', 'n', 'b']);
    }

    #[test]
    fn test_empty_nested_blocks() {
        // a
        // {
        //   {
        //     x
        //   }
        // }
        // b
        let a = command_with_code('a');
        let b = command_with_code('b');
        let x = command_with_code('x');
        let outer_block = command_with_code('{');
        let inner_block = command_with_code('{');

        let head = link_commands(vec![a, outer_block.clone(), b]);
        let outer = link_commands(vec![inner_block.clone()]);
        let inner = link_commands(vec![x]);
        outer_block.borrow_mut().data = CommandData::BranchTarget(outer.clone());
        inner_block.borrow_mut().data = CommandData::BranchTarget(inner.clone());

        patch_block_endings(head.clone());

        assert_eq!(collect_codes(head), vec!['a', '{', 'b']);
        assert_eq!(collect_codes(outer), vec!['{', 'b']);
        assert_eq!(collect_codes(inner), vec!['x', 'b']);
    }

    // compile_read_file_command
    #[test]
    fn test_compile_read_file_command_rejected_under_sandbox() {
        let (mut lines, mut chars) = make_providers("r input.txt");
        let mut cmd = Command::default();
        let mut context = ctx();
        context.sandbox = true;

        let err =
            compile_read_file_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(err.to_string().contains(ERR_SANDBOX));
    }

    #[test]
    // FB-021: `r`'s file is opened when the command *runs*, which for an embedder may be
    // long after (and so against a different process directory than) when the script was
    // compiled. Resolving to an absolute path at compile time, while the directory is
    // still the right one, keeps the later read from landing in the wrong place.
    fn test_compile_read_file_command_resolves_a_relative_path_to_absolute() {
        let (mut lines, mut chars) = make_providers("r input.txt");
        let mut cmd = Command::default();
        let mut context = ctx();

        compile_read_file_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        let CommandData::Path(path) = &cmd.data else {
            panic!("expected CommandData::Path, got {:?}", cmd.data);
        };
        assert!(path.is_absolute(), "{path:?} is not absolute");
        assert_eq!(path.file_name().unwrap(), "input.txt");
    }

    #[test]
    fn test_compile_read_file_command_leaves_an_absolute_path_alone() {
        let (mut lines, mut chars) = make_providers("r /already/absolute.txt");
        let mut cmd = Command::default();
        let mut context = ctx();

        compile_read_file_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        let CommandData::Path(path) = &cmd.data else {
            panic!("expected CommandData::Path, got {:?}", cmd.data);
        };
        assert_eq!(path, std::path::Path::new("/already/absolute.txt"));
    }

    // compile_write_file_command
    #[test]
    fn test_compile_write_file_command_rejected_under_sandbox() {
        let (mut lines, mut chars) = make_providers("w out.txt");
        let mut cmd = Command::default();
        let mut context = ctx();
        context.sandbox = true;

        let err =
            compile_write_file_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(err.to_string().contains(ERR_SANDBOX));
    }

    // compile_label_command
    #[test]
    fn test_compile_label_command() {
        let (mut lines, mut chars) = make_providers(": foo");
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_label_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Label(label) => {
                let name = label.clone().unwrap();
                assert_eq!(name, "foo");
            }
            _ => panic!("Expected CommandData::Label"),
        }
    }

    #[test]
    fn test_compile_missing_label_command() {
        let (mut lines, mut chars) = make_providers(": ;");
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        cmd.code = ':';
        let err =
            compile_label_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap_err();
        assert!(err.to_string().contains("empty label"));
    }

    #[test]
    fn test_compile_empty_label_command() {
        let (mut lines, mut chars) = make_providers("b ;");
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        cmd.code = 'b';
        compile_label_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Label(label) => {
                assert!(label.is_none());
            }
            _ => panic!("Expected CommandData::Label(None)"),
        }
    }

    // populate_label_map
    fn command_with_data(data: CommandData) -> Rc<RefCell<Command>> {
        Rc::new(RefCell::new(Command {
            data,
            ..Default::default()
        }))
    }

    #[test]
    fn test_single_label() {
        let cmd = command_with_data(CommandData::Label(Some("start".to_string())));
        cmd.borrow_mut().code = ':';
        let mut context = ProcessingContext::default();

        populate_label_map(Some(cmd.clone()), &mut context).unwrap();

        assert_eq!(context.label_to_command_map.len(), 1);
        assert!(context.label_to_command_map.contains_key("start"));
        assert!(Rc::ptr_eq(&context.label_to_command_map["start"], &cmd));
    }

    #[test]
    fn test_label_inside_block() {
        let nested = command_with_data(CommandData::Label(Some("inside".to_string())));
        nested.borrow_mut().code = ':';
        let block = command_with_data(CommandData::BranchTarget(Some(nested.clone())));
        let mut context = ProcessingContext::default();

        populate_label_map(Some(block), &mut context).unwrap();

        assert_eq!(context.label_to_command_map.len(), 1);
        assert!(context.label_to_command_map.contains_key("inside"));
        assert!(Rc::ptr_eq(&context.label_to_command_map["inside"], &nested));
    }

    #[test]
    fn test_multiple_labels() {
        let a = command_with_data(CommandData::Label(Some("a".to_string())));
        a.borrow_mut().code = ':';
        let b = command_with_data(CommandData::Label(Some("b".to_string())));
        b.borrow_mut().code = ':';
        let head = link_commands(vec![a, b]);

        let mut context = ProcessingContext::default();
        populate_label_map(head, &mut context).unwrap();

        assert_eq!(context.label_to_command_map.len(), 2);
        assert!(context.label_to_command_map.contains_key("a"));
        assert!(context.label_to_command_map.contains_key("b"));
    }

    #[test]
    fn test_no_labels() {
        let a = command_with_data(CommandData::None);
        let b = command_with_data(CommandData::None);
        let head = link_commands(vec![a, b]);

        let mut context = ProcessingContext::default();
        populate_label_map(head, &mut context).unwrap();

        assert_eq!(context.label_to_command_map.len(), 0);
    }

    #[test]
    fn test_label_none_is_ignored() {
        let cmd = command_with_data(CommandData::Label(None));
        let mut context = ProcessingContext::default();

        populate_label_map(Some(cmd), &mut context).unwrap();

        // The map should remain empty since the label is None
        assert_eq!(context.label_to_command_map.len(), 0);
    }

    #[test]
    fn test_duplicate_label_gives_error() {
        let a1 = command_with_data(CommandData::Label(Some("dup".to_string())));
        a1.borrow_mut().code = ':';

        let a2 = command_with_data(CommandData::Label(Some("dup".to_string())));
        a2.borrow_mut().code = ':';

        let head = link_commands(vec![a1, a2]);
        let mut context = ProcessingContext::default();

        let result = populate_label_map(head, &mut context);

        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("duplicate label `dup'"));
    }

    // populate_range_commands
    fn command_with_range(
        code: char,
        start: usize,
        end: usize,
        data: CommandData,
    ) -> Rc<RefCell<Command>> {
        Rc::new(RefCell::new(Command {
            code,
            addr1: Some(Address::Line(start)),
            addr2: Some(Address::Line(end)),
            data,
            ..Default::default()
        }))
    }

    #[test]
    fn test_range_address() {
        let cmd = command_with_range('p', 3, 5, CommandData::None);
        let mut context = ProcessingContext::default();
        assert_eq!(context.range_commands.len(), 0);

        populate_range_commands(Some(cmd.clone()), &mut context);

        assert_eq!(context.range_commands.len(), 1);

        // Verify it is the same command
        let rc = &context.range_commands[0];
        assert!(Rc::ptr_eq(rc, &cmd));

        // Verify addresses
        let cmd_ref = rc.borrow();

        assert!(matches!(cmd_ref.addr1, Some(Address::Line(3))));
        assert!(matches!(cmd_ref.addr2, Some(Address::Line(5))));
    }

    #[test]
    fn test_non_range_addresses_do_not_register() {
        let mut context = ProcessingContext::default();

        // Zero-address command
        let cmd0 = Rc::new(RefCell::new(Command {
            code: 'p',
            data: CommandData::None,
            ..Default::default()
        }));

        populate_range_commands(Some(cmd0), &mut context);
        assert!(context.range_commands.is_empty());

        // One-address command
        let cmd1 = Rc::new(RefCell::new(Command {
            code: 'p',
            addr1: Some(Address::Line(3)),
            data: CommandData::None,
            ..Default::default()
        }));

        populate_range_commands(Some(cmd1), &mut context);
        assert!(context.range_commands.is_empty());
    }

    #[test]
    fn test_range_address_outside_and_inside_block() {
        // Top-level range command: 1,2p
        let outer = command_with_range('p', 1, 2, CommandData::None);

        // Nested range command: 3,5p
        let nested = command_with_range('p', 3, 5, CommandData::None);

        // Block containing the nested range command
        let block = command_with_data(CommandData::BranchTarget(Some(nested.clone())));

        // Link outer -> block
        outer.borrow_mut().next = Some(block);

        let mut context = ProcessingContext::default();
        assert_eq!(context.range_commands.len(), 0);

        populate_range_commands(Some(outer.clone()), &mut context);

        // Two range commands must be found.
        assert_eq!(context.range_commands.len(), 2);

        // Verify both commands are present (order-independent).
        assert!(
            context
                .range_commands
                .iter()
                .any(|rc| Rc::ptr_eq(rc, &outer))
        );
        assert!(
            context
                .range_commands
                .iter()
                .any(|rc| Rc::ptr_eq(rc, &nested))
        );

        let nested_ref = nested.borrow();

        let addr1 = nested_ref.addr1.as_ref().expect("nested addr1 missing");
        assert!(matches!(addr1, Address::Line(3)));

        let addr2 = nested_ref.addr2.as_ref().expect("nested addr2 missing");
        assert!(matches!(addr2, Address::Line(5)));
    }

    // resolve_branch_targets
    #[test]
    fn test_branch_target_resolved() {
        let target = command_with_data(CommandData::Label(Some("end".to_string())));
        target.borrow_mut().code = ':';

        let branch = command_with_data(CommandData::Label(Some("end".to_string())));
        branch.borrow_mut().code = 'b';

        let head = link_commands(vec![branch.clone(), target.clone()]);
        let mut context = ProcessingContext::default();

        populate_label_map(head.clone(), &mut context).unwrap();
        let result = resolve_branch_targets(head, &mut context);
        assert!(result.is_ok());

        match &branch.borrow().data {
            CommandData::BranchTarget(Some(ptr)) => {
                assert!(Rc::ptr_eq(ptr, &target));
            }
            _ => panic!("Expected BranchTarget(Some(...))"),
        }
    }

    #[test]
    fn test_branch_target_missing_label_gives_error() {
        let branch = command_with_data(CommandData::Label(Some("nope".to_string())));
        branch.borrow_mut().code = 't';

        let mut context = ProcessingContext::default();
        let result = resolve_branch_targets(Some(branch), &mut context);

        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("undefined label `nope'"));
    }

    #[test]
    fn test_branch_with_no_label_resolves_to_none() {
        let branch = command_with_data(CommandData::Label(None));
        branch.borrow_mut().code = 'b';

        let mut context = ProcessingContext::default();
        let result = resolve_branch_targets(Some(branch.clone()), &mut context);

        assert!(result.is_ok());
        match &branch.borrow().data {
            CommandData::BranchTarget(None) => {} // ok
            _ => panic!("Expected BranchTarget(None)"),
        }
    }

    #[test]
    fn test_non_branch_label_is_unchanged() {
        let cmd = command_with_data(CommandData::Label(Some("unchanged".to_string())));
        cmd.borrow_mut().code = 'q'; // not a branch command

        let mut context = ProcessingContext::default();
        let result = resolve_branch_targets(Some(cmd.clone()), &mut context);
        assert!(result.is_ok());

        match &cmd.borrow().data {
            CommandData::Label(Some(label)) => assert_eq!(label, "unchanged"),
            _ => panic!("Expected Label(Some(...)) to remain unchanged"),
        }
    }

    #[test]
    fn test_branch_in_nested_block() {
        let label = command_with_data(CommandData::Label(Some("inner".to_string())));
        label.borrow_mut().code = ':';

        let branch = command_with_data(CommandData::Label(Some("inner".to_string())));
        branch.borrow_mut().code = 't';

        let block = command_with_data(CommandData::BranchTarget(Some(label.clone())));
        let head = link_commands(vec![branch.clone(), block]);

        let mut context = ProcessingContext::default();
        populate_label_map(Some(label.clone()), &mut context).unwrap();
        let result = resolve_branch_targets(head, &mut context);

        assert!(result.is_ok());
        match &branch.borrow().data {
            CommandData::BranchTarget(Some(ptr)) => assert!(Rc::ptr_eq(ptr, &label)),
            _ => panic!("Expected BranchTarget(Some(...))"),
        }
    }

    // compile_text_command
    #[test]
    fn test_compile_single_line_text_command() {
        let mut chars = make_char_provider("a\\");
        let mut lines = make_line_provider(&["line1", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"line1\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_posix_spaces_single_line() {
        let mut chars = make_char_provider("a \\ ");
        let mut lines = make_line_provider(&["line1", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext {
            posix: true,
            ..Default::default()
        };

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"line1\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_posix_incomplete() {
        let (mut lines, mut chars) = make_providers("i\\");
        let mut cmd = Command::default();
        let mut context = ProcessingContext {
            posix: true,
            ..Default::default()
        };
        let result = compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context);
        let err = result.unwrap_err().to_string();
        assert!(err.contains("incomplete command"));
    }

    #[test]
    fn test_compile_text_command_gnu_optional_backslash() {
        let mut chars = make_char_provider("athere");
        let mut lines = make_line_provider(&["line1", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"there\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_gnu_optional_backslash_spaces() {
        let mut chars = make_char_provider("a \t there");
        let mut lines = make_line_provider(&["line1", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"there\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_gnu_no_text() {
        let mut chars = make_char_provider("a");
        let mut lines = make_line_provider(&[]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        let result = compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("expected \\ after `a', `c' or `i'"));
    }

    #[test]
    fn test_compile_text_command_gnu_optional_backslash_escape_eof() {
        let mut chars = make_char_provider("a\\");
        let mut lines = make_line_provider(&[]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_gnu_no_first_escape() {
        let mut chars = make_char_provider("a\\tom");
        let mut lines = make_line_provider(&[]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"tom\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_gnu_char_escapes() {
        let mut chars = make_char_provider("i\\>\\h\\elll\\bo\\nto\\");
        let mut lines = make_line_provider(&["all\\a", ""]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b">helll\x08o\nto\nall\x07\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_gnu_preserves_invalid_utf8_script_byte() {
        let mut chars = ScriptCharProvider::new(b"a\\\xC2");
        let mut lines = make_line_provider(&[]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"\xC2\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_two_line_text_command() {
        let mut chars = make_char_provider("a\\");
        let mut lines = make_line_provider(&["line1\\", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext::default();

        compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context).unwrap();
        match &cmd.data {
            CommandData::Text(text) => {
                assert_eq!(text.as_ref(), b"line1\nline2\n");
            }
            _ => panic!("Expected CommandData::Text"),
        }
    }

    #[test]
    fn test_compile_text_command_posix_without_backslash() {
        let mut chars = make_char_provider("a");
        let mut lines = make_line_provider(&["line1", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext {
            posix: true,
            ..Default::default()
        };

        let result = compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("expected \\ after `a', `c' or `i'"));
    }

    #[test]
    fn test_compile_text_command_posix_with_trailing_chars() {
        let mut chars = make_char_provider("a \\ foo");
        let mut lines = make_line_provider(&["line1", "line2"]);
        let mut cmd = Command::default();
        let mut context = ProcessingContext {
            posix: true,
            ..Default::default()
        };

        let result = compile_text_command(&mut lines, &mut chars, &mut cmd, &mut context);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("extra characters after \\"));
    }

    // read_file_path
    #[test]
    fn test_read_existing_file_path() {
        let (lines, mut chars) = make_providers("r /etc/motd");

        let path = read_file_path(&lines, &mut chars).unwrap();
        assert_eq!(path.to_str().unwrap(), "/etc/motd");
    }

    #[test]
    fn test_read_missing_file_path() {
        let (lines, mut chars) = make_providers("w ");

        let err = read_file_path(&lines, &mut chars).unwrap_err();
        assert!(
            err.to_string()
                .contains("missing filename in r/R/w/W commands")
        );
    }

    #[test]
    #[cfg(not(unix))]
    fn test_read_file_path_rejects_invalid_characters() {
        let lines = ScriptLineProvider::new(vec![]);
        let mut chars = ScriptCharProvider::new(b"w bad\xFFpath");

        let err = read_file_path(&lines, &mut chars).unwrap_err();
        assert!(err.to_string().contains("invalid characters file path"));
    }
}

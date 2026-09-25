//! Provide the script contents line by line
//
// SPDX-License-Identifier: MIT
// Copyright (c) 2025 Diomidis Spinellis
//
// This file is part of the uutils sed package.
// It is licensed under the MIT License.
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use std::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::PathBuf;

use uucore::display::Quotable;
use uucore::error::{FromIo, UResult};

#[derive(Debug, PartialEq)]
/// The specification of a script: through a string or a file
pub enum ScriptValue {
    /// Raw script bytes (`-e`, or the first-POSIX-form positional script argument): bytes, not
    /// `String`, so a raw byte from the shell (e.g. `x=$'\xff'; sed "s/$x/X/"`) survives as
    /// that exact byte, rather than needing to already be valid UTF-8 to reach here at all (a
    /// `String`-typed clap argument turns away anything less with "invalid utf-8 was detected
    /// in one or more arguments" before this code ever runs).
    StringVal(Vec<u8>),
    PathVal(PathBuf),
}

#[derive(Debug)]
/// The provider of script lines across all specified scripts
/// Scripts can be specified to sed as files or as strings.
pub struct ScriptLineProvider {
    sources: Vec<ScriptValue>,
    state: State,
    /// The last `Active` source's own name and line number, kept once `state` has moved past
    /// it (to the next source, or to `Done`) — so a caller reporting "unterminated" once
    /// `next_line` finally returns `None` still names the source that ran out, instead of the
    /// no-current-source defaults `get_input_name`/`get_line_number` would otherwise fall back
    /// to. Verified against the oracle: GNU's own "-e expression #1, char 5: unterminated `s'
    /// command" still names expression #1 even though, by the time it's reported, `-e` #1's
    /// content has already been entirely consumed.
    last_input_name: String,
    last_line_number: usize,
}

/// Encapsulation of the script line provider's state
enum State {
    NotStarted, // Processing has not yet started
    Active {
        index: usize,
        reader: Box<dyn BufRead>, // Object on which read_line is called
        input_name: String,       // Input description (path or script string)
        line_number: usize,       // Current line number
    },
    Done, // All scripts have been processed
}

impl ScriptLineProvider {
    /// Construct the script provider from the specified script sources
    pub fn new(sources: Vec<ScriptValue>) -> Self {
        Self {
            sources,
            state: State::NotStarted,
            last_input_name: String::new(),
            last_line_number: 0,
        }
    }

    /// Return the currently processed script line number, or the last one that was active if
    /// none is right now (see `last_line_number`'s own comment).
    pub fn get_line_number(&self) -> usize {
        match &self.state {
            State::Active { line_number, .. } => *line_number,
            _ => self.last_line_number,
        }
    }

    /// Return the currently processed script descriptive name, or the last one that was active
    /// if none is right now (see `last_input_name`'s own comment).
    pub fn get_input_name(&self) -> &str {
        match &self.state {
            State::Active { input_name, .. } => input_name.as_str(),
            _ => &self.last_input_name,
        }
    }

    /// Return the next script line to process across all scripts.
    pub fn next_line(&mut self) -> UResult<Option<Vec<u8>>> {
        let mut line = Vec::new();

        loop {
            let advance = match &mut self.state {
                State::NotStarted => Some(0),
                State::Active {
                    index,
                    reader,
                    line_number,
                    ..
                } => {
                    line.clear();
                    let bytes = reader.read_until(b'\n', &mut line)?;
                    if bytes == 0 {
                        Some(*index + 1) // finished reading this source
                    } else {
                        *line_number += 1;
                        // Remove trailing newline
                        if line.ends_with(b"\n") {
                            line.pop();
                        }
                        return Ok(Some(line));
                    }
                }
                State::Done => {
                    return Ok(None);
                }
            };

            if let Some(next_index) = advance {
                self.advance_source(next_index)?;
            }
        }
    }

    // Move to the next available script source.
    fn advance_source(&mut self, next_index: usize) -> UResult<()> {
        // Remember this source's own name and line number (see `last_input_name`'s own
        // comment) before leaving it, whether for the next source or for `Done`.
        if let State::Active {
            input_name,
            line_number,
            ..
        } = &self.state
        {
            self.last_input_name.clone_from(input_name);
            self.last_line_number = *line_number;
        }

        if next_index >= self.sources.len() {
            self.state = State::Done;
            return Ok(());
        }

        match &self.sources[next_index] {
            ScriptValue::StringVal(s) => {
                let cursor = std::io::Cursor::new(s.clone());
                self.state = State::Active {
                    index: next_index,
                    reader: Box::new(BufReader::new(cursor)),
                    input_name: format!("<script argument {}>", next_index + 1),
                    line_number: 0,
                };
            }
            ScriptValue::PathVal(p) => {
                if p.to_string_lossy() == "-" {
                    self.state = State::Active {
                        index: next_index,
                        reader: Box::new(BufReader::new(io::stdin())),
                        input_name: "<stdin>".to_string(),
                        line_number: 0,
                    };
                } else {
                    let file = File::open(p)
                        .map_err_context(|| format!("error opening script file {}", p.quote()))?;
                    self.state = State::Active {
                        index: next_index,
                        reader: Box::new(BufReader::new(file)),
                        input_name: p.to_string_lossy().to_string(),
                        line_number: 0,
                    };
                }
            }
        }

        Ok(())
    }
}

impl fmt::Debug for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            State::NotStarted => f.debug_struct("NotStarted").finish(),
            State::Done => f.debug_struct("Done").finish(),
            State::Active {
                index,
                input_name,
                line_number,
                ..
            } => f
                .debug_struct("Active")
                .field("index", index)
                .field("input_name", input_name)
                .field("line_number", line_number)
                .field("reader", &"<BufRead>")
                .finish(),
        }
    }
}

#[cfg(test)]
impl ScriptLineProvider {
    pub fn with_active_state(input_name: &str, line_number: usize) -> Self {
        Self {
            sources: vec![],
            state: State::Active {
                input_name: input_name.to_string(),
                line_number,
                index: 0,
                reader: Box::new(BufReader::new(io::stdin())),
            },
            last_input_name: String::new(),
            last_line_number: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_string_source() {
        let input = vec![
            ScriptValue::StringVal(b"line one\nline two\n".to_vec()),
            ScriptValue::StringVal(b"line three".to_vec()),
        ];
        let mut provider = ScriptLineProvider::new(input);

        let mut lines = Vec::new();
        while let Some(line) = provider.next_line().unwrap() {
            lines.push(String::from_utf8(line).unwrap().trim_end().to_string());
        }

        assert_eq!(lines, vec!["line one", "line two", "line three"]);
    }

    #[test]
    fn test_file_source() {
        let mut temp_file = NamedTempFile::new().unwrap();
        writeln!(temp_file, "file line 1").unwrap();
        writeln!(temp_file, "file line 2").unwrap();

        let input = vec![ScriptValue::PathVal(temp_file.path().to_path_buf())];
        let mut provider = ScriptLineProvider::new(input);

        let mut lines = Vec::new();
        while let Some(line) = provider.next_line().unwrap() {
            lines.push(String::from_utf8(line).unwrap().trim_end().to_string());
        }

        assert_eq!(lines, vec!["file line 1", "file line 2"]);
    }

    #[test]
    fn test_mixed_source() {
        let mut temp_file = NamedTempFile::new().unwrap();
        writeln!(temp_file, "file line 1").unwrap();
        writeln!(temp_file, "file line 2").unwrap();
        let temp_file2 = NamedTempFile::new().unwrap();

        let input = vec![
            ScriptValue::PathVal(temp_file.path().to_path_buf()),
            ScriptValue::StringVal(b"script line 1".to_vec()),
            ScriptValue::PathVal(temp_file.path().to_path_buf()),
            ScriptValue::StringVal(Vec::new()),
            ScriptValue::PathVal(temp_file2.path().to_path_buf()),
            ScriptValue::StringVal(b"other script line 1".to_vec()),
        ];
        let mut provider = ScriptLineProvider::new(input);

        let mut lines = Vec::new();
        while let Some(line) = provider.next_line().unwrap() {
            lines.push(String::from_utf8(line).unwrap().trim_end().to_string());
        }

        assert_eq!(
            lines,
            vec![
                "file line 1",
                "file line 2",
                "script line 1",
                "file line 1",
                "file line 2",
                "other script line 1",
            ]
        );
    }

    #[test]
    fn test_getters() {
        let input = vec![
            ScriptValue::StringVal(b"l1\nl2\n".to_vec()),
            ScriptValue::StringVal(b"l3".to_vec()),
        ];
        let mut provider = ScriptLineProvider::new(input);

        if let Some(line) = provider.next_line().unwrap() {
            assert_eq!(String::from_utf8(line).unwrap().trim(), "l1");
            assert_eq!(provider.get_line_number(), 1);
            assert_eq!(provider.get_input_name(), "<script argument 1>");
        } else {
            panic!("Expected a line");
        }

        if let Some(line) = provider.next_line().unwrap() {
            assert_eq!(String::from_utf8(line).unwrap().trim(), "l2");
            assert_eq!(provider.get_line_number(), 2);
            assert_eq!(provider.get_input_name(), "<script argument 1>");
        } else {
            panic!("Expected a line");
        }

        if let Some(line) = provider.next_line().unwrap() {
            assert_eq!(String::from_utf8(line).unwrap().trim(), "l3");
            assert_eq!(provider.get_line_number(), 1);
            assert_eq!(provider.get_input_name(), "<script argument 2>");
        } else {
            panic!("Expected a line");
        }
    }

    #[test]
    fn test_file_source_preserves_invalid_utf8_bytes() {
        let mut temp_file = NamedTempFile::new().unwrap();
        temp_file.write_all(b"s/\xC2\xE7/X/\n").unwrap();

        let input = vec![ScriptValue::PathVal(temp_file.path().to_path_buf())];
        let mut provider = ScriptLineProvider::new(input);

        assert_eq!(provider.next_line().unwrap().unwrap(), b"s/\xC2\xE7/X/");
    }
}

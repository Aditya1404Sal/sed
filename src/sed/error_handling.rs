// Parse delimited character sequences
//
// SPDX-License-Identifier: MIT
// Copyright (c) 2025 Diomidis Spinellis
//
// This file is part of the uutils sed package.
// It is licensed under the MIT License.
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use crate::sed::command::ProcessingContext;
use crate::sed::script_char_provider::ScriptCharProvider;
use crate::sed::script_line_provider::ScriptLineProvider;

use std::rc::Rc;

use uucore::display::Quotable;
use uucore::error::{UResult, USimpleError};

#[derive(Clone, Debug)]
/// The location in a script where a command is defined
pub struct ScriptLocation {
    pub input_name: Rc<str>,  // Shared input name
    pub line_number: usize,   // 1-based line number
    pub column_number: usize, // 1-based column number
}

impl Default for ScriptLocation {
    fn default() -> Self {
        ScriptLocation {
            input_name: Rc::from("<unknown>"),
            line_number: 1,
            column_number: 1,
        }
    }
}

impl ScriptLocation {
    /// Construct with position information from the given providers.
    pub fn at_position(lines: &ScriptLineProvider, line: &ScriptCharProvider) -> Self {
        ScriptLocation {
            line_number: lines.get_line_number(),
            column_number: char_column(line),
            input_name: Rc::from(lines.get_input_name()),
        }
    }
}

/// GNU's own location prefix for a diagnostic tied to a specific point in the script source,
/// without the trailing `: ` before the message text — verified against the oracle:
/// `-e expression #1, char 5: unterminated `s' command` for the first `-e` (or the
/// first-POSIX-form positional script argument, which GNU labels the same way), or
/// `-e expression #2, char 4: ...` for a later `-e`, each with its own 1-based char column
/// (not a running total across `-e`s, and no line number at all — GNU only counts characters
/// within the one expression). `input_name` here is `ScriptLineProvider::get_input_name`'s own
/// `<script argument N>` marker (`advance_source`, `script_line_provider.rs`) for exactly this
/// case; anything else (a `-f` script file) falls back to the pre-existing, generic
/// `name:line:col: error` form, since GNU's own file-sourced wording hasn't been verified here.
pub(crate) fn location_prefix(input_name: &str, line_number: usize, column: usize) -> String {
    match input_name
        .strip_prefix("<script argument ")
        .and_then(|rest| rest.strip_suffix('>'))
    {
        Some(index) => format!("-e expression #{index}, char {column}"),
        None => format!("{input_name}:{line_number}:{column}: error"),
    }
}

/// Fail with msg as a compile error at the provider location.
/// The error's exit code is 1 (compilation phase).
pub fn compilation_error<T>(
    lines: &ScriptLineProvider,
    line: &ScriptCharProvider,
    msg: impl ToString,
) -> UResult<T> {
    Err(USimpleError::new(
        1,
        format!(
            "{}: {}",
            location_prefix(
                lines.get_input_name(),
                lines.get_line_number(),
                char_column(line)
            ),
            msg.to_string()
        ),
    ))
}

/// The 1-based column `compilation_error`/`location_error` report: `line.get_pos() + 1`
/// (the position of the character about to be read) everywhere except at end of line, where
/// GNU's own column never runs past the line's own length — verified against the oracle
/// (`sed 's/a/b'`, 5 characters, error `char 5`, not `char 6`).
fn char_column(line: &ScriptCharProvider) -> usize {
    if line.eol() {
        line.get_pos()
    } else {
        line.get_pos() + 1
    }
}

/// Fail with msg as a compilation error at the command's location.
/// The error's exit code is as specified.
fn location_error<T>(location: &ScriptLocation, msg: impl ToString, exit_code: i32) -> UResult<T> {
    Err(USimpleError::new(
        exit_code,
        format!(
            "{}: {}",
            location_prefix(
                &location.input_name,
                location.line_number,
                location.column_number,
            ),
            msg.to_string()
        ),
    ))
}

/// Fail with msg as a compilation error at the command's location.
/// The error's exit code is 1 (compilation phase).
pub fn semantic_error<T>(location: &ScriptLocation, msg: impl ToString) -> UResult<T> {
    location_error(location, msg, 1)
}

/// Fail with msg as a runtime error at the command's location.
/// The error's exit code is 2 (processing phase).
pub fn runtime_error<T>(location: &ScriptLocation, msg: impl ToString) -> UResult<T> {
    location_error(location, msg, 2)
}

/// Fail with msg as a runtime error at the command's and input's location.
/// This is to be used in cases where the error depends on both, for example,
/// a fancy regular expression applied on invalid UTF-8 input.
/// (A fixed string match will not err in this case.)
/// The error's exit code is 2 (processing phase).
pub fn input_runtime_error<T>(
    location: &ScriptLocation,
    context: &ProcessingContext,
    msg: impl ToString,
) -> UResult<T> {
    Err(USimpleError::new(
        2,
        format!(
            "{}:{}:{}: {}:{} error: {}",
            location.input_name,
            location.line_number,
            location.column_number,
            context.input_name.quote(),
            context.line_number,
            msg.to_string()
        ),
    ))
}

/// Replace a `compilation_error`'s own generic message with a context-specific one, keeping
/// its location prefix and exit code — used where `parse_regex_for_mode`/`parse_character_class`
/// raise the same "unterminated regular expression"/"Unterminated bracket expression" whether
/// they were called for a command address or an `s` command's pattern, but GNU's own wording
/// for hitting end of input differs by which one it was (verified against the oracle:
/// `sed '/unterminated'` -> "unterminated address regex", `sed 's/a'` -> `` unterminated `s'
/// command ``, both including for an unterminated bracket expression within the regex).
pub fn remap_unterminated<T>(result: UResult<T>, replacement: &str) -> UResult<T> {
    result.map_err(|error| {
        let message = error.to_string();
        for generic in [
            "unterminated regular expression",
            "Unterminated bracket expression",
        ] {
            if let Some(prefix) = message.strip_suffix(generic) {
                return USimpleError::new(1, format!("{prefix}{replacement}"));
            }
        }
        error
    })
}

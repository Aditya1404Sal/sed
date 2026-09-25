// Support for in-place editing
//
// SPDX-License-Identifier: MIT
// Copyright (c) 2025 Diomidis Spinellis
//
// This file is part of the uutils sed package.
// It is licensed under the MIT License.
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use std::fs;
use std::io::stdout;
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use tempfile::NamedTempFile;
use uucore::display::Quotable;
use uucore::error::{FromIo, UIoError, UResult, USimpleError};

use crate::sed::command::ProcessingContext;
use crate::sed::fast_io::OutputBuffer;

/// Context for in-place editing
pub struct InPlace {
    pub output: OutputBuffer,
    pub in_place: bool,
    pub in_place_suffix: Option<String>,
    pub follow_symlinks: bool,
    pub temp_file: Option<NamedTempFile>,
    pub original_path: Option<PathBuf>,
    /// The record terminator every `OutputBuffer` this constructs should use: NUL with `-z`,
    /// else newline (`OutputBuffer::set_delimiter`'s own default). Stored here since
    /// `begin_resolved` constructs a fresh `OutputBuffer` per file and no longer has the
    /// original `ProcessingContext` once `new` has moved its other fields out of it.
    delimiter: u8,
    /// `-s`/`-i` (`context.separate`): whether each file is addressed (and, it turns out,
    /// terminated) as its own stream rather than one continuous one — see `begin_resolved`'s
    /// own comment for why this changes whether the `!self.in_place` branch may reuse the
    /// existing `OutputBuffer`.
    separate: bool,
}

impl InPlace {
    /// Create an in-place editing engine based on ProcessingContext.
    /// Depending on its settings it may or may not perform in-place
    /// editing, backup the original file, or follow symlinks.
    pub fn new(context: ProcessingContext) -> Self {
        let delimiter = if context.null_data { b'\0' } else { b'\n' };
        let mut output = OutputBuffer::new(Box::new(stdout()));
        output.set_delimiter(delimiter);
        Self {
            output,
            in_place: context.in_place,
            in_place_suffix: context.in_place_suffix,
            follow_symlinks: context.follow_symlinks,
            temp_file: None,
            original_path: None,
            delimiter,
            separate: context.separate,
        }
    }

    /// Return an OutputBuffer for outputting the edits to the specified file.
    /// The file may be a symbolic link, which will be processed according
    /// to the context specification.
    pub fn begin(&mut self, file_name: &Path) -> UResult<&mut OutputBuffer> {
        let resolved = if self.follow_symlinks {
            fs::canonicalize(file_name)
                .map_err_context(|| format!("resolving symlink {}", file_name.quote()))?
        } else {
            file_name.to_path_buf()
        };
        self.begin_resolved(&resolved)
    }

    /// Return an OutputBuffer for outputting the edits to the specified file.
    /// The passed file name should have resolved symbolic links according
    /// to the context settings.
    fn begin_resolved(&mut self, file_name: &Path) -> UResult<&mut OutputBuffer> {
        if !self.in_place {
            // Every file writes to the same stdout here (this is `-s` without `-i`, or the
            // plain single-stream case), but whether a fresh `OutputBuffer` should replace
            // the existing one differs by mode — verified against the oracle both ways:
            //
            // - `-s` (`self.separate`): each file is its own stream, and if its last line
            //   lacked a delimiter, GNU still writes one before the next file's own output
            //   starts — reuse `self.output` so its `pending_newline` (see
            //   `fast_io::OutputBuffer::write_chunk`) carries that decision across the
            //   `in_place.begin()` call between files, whether or not `N` was involved.
            // - Without `-s`: files form one continuous stream, and this fixture-verified
            //   case (`test_multiple_input_files`) shows GNU does NOT insert one — an
            //   unterminated non-final file's content is simply followed immediately by the
            //   next file's, byte for byte. A fresh `OutputBuffer` here means any
            //   `pending_newline` from the file just finished is silently dropped instead of
            //   carried forward, which happens to be exactly the behavior this case needs.
            if !self.separate {
                self.output = OutputBuffer::new(Box::new(stdout()));
                self.output.set_delimiter(self.delimiter);
            }
            return Ok(&mut self.output);
        }

        let metadata = fs::metadata(file_name).map_err_context(|| {
            format!(
                "error Reading metadata of {} for in-place edit",
                file_name.quote()
            )
        })?;

        if !metadata.is_file() {
            return Err(USimpleError::new(
                2,
                format!(
                    "cannot in-place edit non-regular file {}",
                    file_name.quote()
                ),
            ));
        }

        let dir = file_name.parent().unwrap_or_else(|| Path::new("."));
        let temp_file = NamedTempFile::new_in(dir)
            .map_err_context(|| format!("error creating temporary file in {}", dir.quote()))?;

        // TODO: On Unix use fchown(metadata.{uid,dig}) and fchmod(mode)
        // on let fd = temp_file.as_file().as_raw_fd() when uucore::libc
        // support them.
        #[cfg(unix)]
        {
            let mode = metadata.mode() & 0o7777;
            let perms = fs::Permissions::from_mode(mode);
            fs::set_permissions(temp_file.path(), perms)?;
        }

        let mut output = OutputBuffer::new(Box::new(
            temp_file.reopen().expect("reopening NamedTempFile"),
        ));
        output.set_delimiter(self.delimiter);
        self.output = output;
        self.temp_file = Some(temp_file);
        self.original_path = Some(file_name.to_path_buf());

        Ok(&mut self.output)
    }

    /// Finish (potentially in-place) editing.
    pub fn end(&mut self) -> UResult<()> {
        self.output.flush()?;

        if !self.in_place {
            return Ok(());
        }

        let orig = self.original_path.take().expect("original_path unset");
        let temp = self.temp_file.take().expect("temp_file unset");

        // Backup original if suffix is provided
        if let Some(ref suffix) = self.in_place_suffix {
            let mut backup_path = orig.clone();
            let file_name = backup_path
                .file_name()
                .expect("Missing file name for backup")
                .to_os_string();
            let mut backup_name = file_name;
            backup_name.push(suffix);
            backup_path.set_file_name(backup_name);

            #[cfg(windows)]
            // Try to remove to ensure the rename won't fail on Windows.
            let _ = fs::remove_file(&backup_path);

            fs::rename(&orig, &backup_path).map_err_context(|| {
                format!(
                    "error backing up {} to {}",
                    orig.quote(),
                    backup_path.quote()
                )
            })?;
        } else {
            #[cfg(windows)]
            // On Windows delete the original file for temp.persist to work
            if orig.exists() {
                fs::remove_file(&orig).map_err_context(|| {
                    format!("error removing original input file {}", orig.quote())
                })?;
            }
        }

        // Atomically replace the original
        match temp.persist(&orig) {
            Ok(_) => {}
            Err(e) => {
                return Err(UIoError::new(
                    e.error.kind(),
                    format!(
                        "error persisting temporary file {} to {}",
                        e.file.path().quote(),
                        orig.quote()
                    ),
                ));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_fs::TempDir;
    use assert_fs::fixture::PathChild;
    use std::fs;
    use std::io::{Read, Write};
    use std::path::Path;

    fn minimal_context() -> ProcessingContext {
        ProcessingContext {
            in_place: false,
            in_place_suffix: None,
            follow_symlinks: false,
            // fill in default values for the rest as needed
            ..Default::default()
        }
    }

    fn write_original(file: &Path, content: &str) {
        fs::write(file, content).unwrap();
    }

    fn read_file(file: &Path) -> String {
        let mut contents = String::new();
        fs::File::open(file)
            .unwrap()
            .read_to_string(&mut contents)
            .unwrap();
        contents
    }

    #[test]
    fn test_in_place_editing() {
        let temp = TempDir::new().unwrap();
        let file = temp.child("file.txt");
        write_original(file.path(), "original\n");

        let mut ctx = minimal_context();
        ctx.in_place = true;

        let mut inplace = InPlace::new(ctx);
        let buf = inplace.begin(file.path()).unwrap();
        writeln!(buf, "updated").unwrap();
        inplace.end().unwrap();

        assert_eq!(read_file(file.path()), "updated\n");
    }

    #[test]
    fn test_in_place_backup() {
        let temp = TempDir::new().unwrap();
        let file = temp.child("file.txt");
        let backup = temp.child("file.txt.bak");
        write_original(file.path(), "original\n");

        let mut ctx = minimal_context();
        ctx.in_place = true;
        ctx.in_place_suffix = Some(".bak".to_string());

        let mut inplace = InPlace::new(ctx);
        let buf = inplace.begin(file.path()).unwrap();
        writeln!(buf, "new content").unwrap();
        inplace.end().unwrap();

        assert_eq!(read_file(file.path()), "new content\n");
        assert_eq!(read_file(backup.path()), "original\n");
    }

    #[cfg(unix)]
    #[test]
    fn test_symlink_follow_true() {
        let temp = TempDir::new().unwrap();
        let real = temp.child("target.txt");
        let link = temp.child("link.txt");

        write_original(real.path(), "real\n");
        std::os::unix::fs::symlink(real.path(), link.path()).unwrap();

        let mut ctx = minimal_context();
        ctx.in_place = true;
        ctx.follow_symlinks = true;

        let mut inplace = InPlace::new(ctx);
        let buf = inplace.begin(link.path()).unwrap();
        writeln!(buf, "changed").unwrap();
        inplace.end().unwrap();

        assert_eq!(read_file(real.path()), "changed\n");
        assert!(link.path().exists()); // Symlink still exists
    }

    #[cfg(unix)]
    #[test]
    fn test_symlink_follow_false() {
        let temp = TempDir::new().unwrap();
        let real = temp.child("target.txt");
        let link = temp.child("link.txt");

        write_original(real.path(), "real\n");
        std::os::unix::fs::symlink(real.path(), link.path()).unwrap();

        let mut ctx = minimal_context();
        ctx.in_place = true;
        ctx.follow_symlinks = false;

        let mut inplace = InPlace::new(ctx);
        let buf = inplace.begin(link.path()).unwrap();
        writeln!(buf, "linked").unwrap();
        inplace.end().unwrap();

        // real file should remain untouched
        assert_eq!(read_file(real.path()), "real\n");

        // link (symlink path) now contains the new content
        let contents = read_file(link.path());
        assert_eq!(contents, "linked\n");
    }

    #[test]
    fn test_no_in_place_outputs_to_stdout() {
        let mut ctx = minimal_context();
        ctx.in_place = false;

        let mut inplace = InPlace::new(ctx);
        let _buf = inplace.begin(Path::new("fake.txt")).unwrap();
        assert!(inplace.end().is_ok());
    }
}

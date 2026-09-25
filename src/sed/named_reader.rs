// An abstraction for the `R` command's one-line-at-a-time input file
//
// SPDX-License-Identifier: MIT
//
// This file is part of the uutils sed package.
// It is licensed under the MIT License.
// For the full copyright and license information, please view the LICENSE
// file that was distributed with this source code.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

/// A file `R` reads forward through, one line per invocation. GNU sed treats a file that
/// doesn't exist or can't be read as empty rather than an error, so opening happens once,
/// lazily, and any failure just means every future read finds nothing.
#[derive(Debug)]
pub struct NamedReader {
    pub path: PathBuf,
    reader: Option<BufReader<File>>,
}

impl NamedReader {
    /// Open `path` for line-at-a-time reading. Never fails: a missing or unreadable file
    /// just means [`NamedReader::next_line`] always returns `None`, as GNU sed does.
    pub fn new(path: PathBuf) -> Self {
        let reader = File::open(&path).ok().map(BufReader::new);
        Self { path, reader }
    }

    /// Return the next line, its trailing newline included when the file has one, or
    /// `None` once the file is exhausted (or was never readable).
    pub fn next_line(&mut self) -> std::io::Result<Option<Vec<u8>>> {
        let Some(reader) = self.reader.as_mut() else {
            return Ok(None);
        };
        let mut line = Vec::new();
        let n = reader.read_until(b'\n', &mut line)?;
        if n == 0 {
            return Ok(None);
        }
        Ok(Some(line))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn file_with(content: &[u8]) -> NamedTempFile {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(content).unwrap();
        file
    }

    #[test]
    fn reads_one_line_at_a_time() {
        let file = file_with(b"one\ntwo\nthree");
        let mut reader = NamedReader::new(file.path().to_path_buf());
        assert_eq!(reader.next_line().unwrap(), Some(b"one\n".to_vec()));
        assert_eq!(reader.next_line().unwrap(), Some(b"two\n".to_vec()));
        assert_eq!(reader.next_line().unwrap(), Some(b"three".to_vec()));
        assert_eq!(reader.next_line().unwrap(), None);
    }

    #[test]
    fn missing_file_reads_as_empty() {
        let mut reader = NamedReader::new(PathBuf::from("/nonexistent/does-not-exist"));
        assert_eq!(reader.next_line().unwrap(), None);
    }
}

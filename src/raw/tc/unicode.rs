// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The `\u{…}` escapes of a string literal in a term, in the dialects that read them (#175).
//!
//! SMT-LIB §3.1 says a string literal has no escape but `""`: "`\n`, `\012`, `\x0A`, and `\u0008`
//! are not escape sequences". The Unicode Strings theory reads `\u` escapes for its own values,
//! though, and so does ATSLIB ([`Dialect::STRING_UNICODE_ESCAPES`](crate::ast::Dialect)), by
//! decision:
//!
//! - only the braced forms `\u{d}` … `\u{ddddd}`, with one to five hexadecimal digits, denoting a
//!   code point up to `0x2FFFF` that is not a surrogate;
//! - not the theory's unbraced `\udddd`, so `"\u0041"` is six characters;
//! - anything else stays as written: `"\u33yy"`, `"\u{2CA"`, `"\u{30000}"`, `"\n"`.
//!
//! Only string literals in terms are decoded; those elsewhere, e.g. of attributes, `echo` or
//! `set-info`, are kept as written.

use std::borrow::Cow;

/// The largest code point of the Unicode Strings theory's alphabet: planes 0 to 2.
const MAX_STRING_CODE: u32 = 0x2FFFF;

/// The most hexadecimal digits a braced escape has.
const MAX_DIGITS: usize = 5;

/// Decode the `\u{…}` escapes of a string literal's content, whose `""` are already read as `"`.
///
/// A decoded character is not read again, so `"\u{5c}u{41}"` is `\u{41}`, seven characters.
pub(crate) fn decode_unicode_escapes(s: &str) -> Cow<'_, str> {
    if !s.contains("\\u{") {
        return Cow::Borrowed(s);
    }
    let cs: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < cs.len() {
        match braced_escape(&cs[i..]) {
            Some((len, decoded)) => {
                match decoded {
                    Some(c) => out.push(c),
                    None => out.extend(&cs[i..i + len]),
                }
                i += len;
            }
            None => {
                out.push(cs[i]);
                i += 1;
            }
        }
    }
    Cow::Owned(out)
}

/// Whether `cs` begins with a braced escape `\u{…}`, with one to five characters between the
/// braces: if so, its length, and the character it denotes, if it denotes one.
///
/// The escape ends at the *first* `}` that leaves one to five characters
/// between the braces, and if those are not the digits of a character, the whole sequence is
/// kept as written: `\u{\u{41}}` is no escape, and neither is the `\u{41}` inside it.
fn braced_escape(cs: &[char]) -> Option<(usize, Option<char>)> {
    if cs.get(..3)? != ['\\', 'u', '{'] {
        return None;
    }
    let digits = (1..=MAX_DIGITS).find(|&n| cs.get(3 + n) == Some(&'}'))?;
    let decoded = code_point(&cs[3..3 + digits]);
    Some((3 + digits + 1, decoded))
}

/// The character the hexadecimal `digits` denote, if they are digits and denote one in the
/// theory's alphabet.
fn code_point(digits: &[char]) -> Option<char> {
    let mut v: u32 = 0;
    for d in digits {
        v = v * 16 + d.to_digit(16)?;
    }
    if v > MAX_STRING_CODE {
        return None;
    }
    char::from_u32(v)
}

#[cfg(test)]
mod tests {
    use super::decode_unicode_escapes;

    fn decode(s: &str) -> String {
        decode_unicode_escapes(s).into_owned()
    }

    /// The examples of the decision.
    #[test]
    fn test_decided_examples() {
        assert_eq!(decode(r"\u{48}I"), "HI");
        assert_eq!(decode(r"\u0041"), r"\u0041");
        assert_eq!(decode(r"\u33yy"), r"\u33yy");
        assert_eq!(decode(r"\n"), r"\n");
    }

    #[test]
    fn test_digit_counts() {
        assert_eq!(decode(r"\u{9}"), "\t");
        assert_eq!(decode(r"\u{41}"), "A");
        assert_eq!(decode(r"\u{3bb}"), "λ");
        assert_eq!(decode(r"\u{1F600}"), "😀");
        assert_eq!(decode(r"\u{2FFFF}"), "\u{2FFFF}");
        assert_eq!(decode(r"\u{0}"), "\0");
        assert_eq!(decode(r"\u{00041}"), "A");
        assert_eq!(decode(r"\u{aB}"), "\u{ab}");
        // six digits are too many
        assert_eq!(decode(r"\u{000041}"), r"\u{000041}");
    }

    #[test]
    fn test_kept_as_written() {
        for s in [
            r"\u{}",
            r"\u{2CA",
            r"\u{",
            r"\u",
            r"\",
            r"\u{30000}",
            r"\u{D800}",
            r"\u{dfff}",
            r"\u{4g}",
            r"\u{ 41}",
            r"\U{41}",
            r"\x41",
            r"\u{\u{41}}",
        ] {
            assert_eq!(decode(s), s, "{s}");
        }
    }

    #[test]
    fn test_in_context() {
        assert_eq!(decode(r"a\u{62}c\u{64}"), "abcd");
        assert_eq!(decode(r#"say \u{22}hi\u{22}"#), "say \"hi\"");
        // a decoded backslash is not read again
        assert_eq!(decode(r"\u{5c}u{41}"), r"\u{41}");
        assert_eq!(decode(r"\\u{41}"), r"\A");
        assert_eq!(decode(r"\u{41}}"), "A}");
        assert_eq!(decode(r"\u{2CA\u{41}"), r"\u{2CAA");
        assert_eq!(decode("ü\\u{fc}"), "üü");
    }
}

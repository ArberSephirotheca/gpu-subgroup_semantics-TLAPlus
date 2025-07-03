use super::syntax::TokenKind;
use std::fmt;
use text_size::TextRange;
pub enum AsukaError {
    ParseError(String, TokenKind),
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParseError {
    pub(super) expected: Vec<TokenKind>,
    pub(super) found: Option<TokenKind>,
    pub(super) range: TextRange,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "error at {}..{}: expected ",
            u32::from(self.range.start()),
            u32::from(self.range.end()),
        )?;

        for (idx, expected_kind) in self.expected.iter().enumerate() {
            if idx == 0 {
                write!(f, "{}", expected_kind)?;
            } else if idx == self.expected.len() - 1 {
                write!(f, " or {}", expected_kind)?;
            } else {
                write!(f, ", {}", expected_kind)?;
            }
        }

        if let Some(found) = self.found {
            write!(f, ", but found {}", found)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Range as StdRange;

    fn check(
        expected: Vec<TokenKind>,
        found: Option<TokenKind>,
        range: StdRange<u32>,
        output: &str,
    ) {
        let error = ParseError {
            expected,
            found,
            range: {
                let start = range.start.into();
                let end = range.end.into();
                TextRange::new(start, end)
            },
        };

        assert_eq!(format!("{}", error), output);
    }

    // #[test]
    // fn one_expected_did_find() {
    //     check(
    //         vec![TokenKind::Equal],
    //         Some(TokenKind::Ident),
    //         10..20,
    //         "error at 10..20: expected ‘=’, but found identifier",
    //     );
    // }
}

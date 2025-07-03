use super::parser_error::ParseError;
use crate::compiler::parse::syntax::TokenKind;
// Make our parser event base.
// The benefit of Event-driven parser is that it makes parser faster
// if we have a previous parse tree lying around.
// It also makes the parser and syntax tree easier to modify.
#[derive(Debug, Clone, PartialEq)]
pub enum Event {
    StartNode {
        kind: TokenKind,
        forward_parent: Option<usize>,
        line: usize,
    },
    StartNodeAt {
        kind: TokenKind,
        checkpoint: usize,
    },
    AddToken {
        token_index: usize,
    },
    FinishNode,
    Placeholder,
    Error(ParseError),
}

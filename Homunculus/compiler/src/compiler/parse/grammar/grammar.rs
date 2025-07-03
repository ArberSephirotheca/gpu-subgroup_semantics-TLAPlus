use crate::compiler::parse::{marker::CompletedMarker, parser::Parser, syntax::TokenKind};

use super::statement::stmt;

pub(crate) fn root(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    while !p.at_end() {
        stmt(p);
    }
    m.complete(p, TokenKind::Root, p.get_line())
}

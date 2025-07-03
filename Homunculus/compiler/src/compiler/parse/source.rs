use super::syntax::TokenKind;
use crate::compiler::parse::lexer::Token;
use text_size::TextRange;
pub(crate) struct Source<'l, 't> {
    tokens: &'l [Token<'t>],
    cursor: usize,
}

impl<'l, 't> Source<'l, 't> {
    pub(super) fn new(tokens: &'l [Token<'t>]) -> Self {
        Self { tokens, cursor: 0 }
    }

    pub(super) fn next_token(&mut self) -> Option<&'l Token<'t>> {
        self.eat_trivial();

        let token = self.tokens.get(self.cursor)?;
        self.cursor += 1;

        Some(token)
    }

    pub(super) fn peek_kind(&mut self) -> Option<TokenKind> {
        self.eat_trivial();
        self.peek_kind_raw()
    }
    pub(crate) fn peek_token(&mut self) -> Option<&Token> {
        self.eat_trivial();
        self.peek_token_raw()
    }

    fn eat_trivial(&mut self) {
        while self.peek_kind_raw().map_or(false, TokenKind::is_trivial) {
            self.cursor += 1;
        }
    }

    fn peek_kind_raw(&self) -> Option<TokenKind> {
        self.peek_token_raw()
            .map(|Token { kind, .. }| (*kind).into())
    }

    fn peek_token_raw(&self) -> Option<&Token> {
        self.tokens.get(self.cursor)
    }

    pub(crate) fn last_token_range(&self) -> Option<TextRange> {
        self.tokens.last().map(|Token { range, .. }| *range)
    }
}

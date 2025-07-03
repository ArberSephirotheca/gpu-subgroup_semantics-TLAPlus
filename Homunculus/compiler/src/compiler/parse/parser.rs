use super::grammar::grammar;
use super::marker::Marker;
use super::syntax::SyntaxToken;
use super::{
    event::Event, lexer::Lexer, parser_error::AsukaError, parser_error::ParseError, sink::Sink,
};
use crate::compiler::parse::lexer::Token;
use crate::compiler::parse::source::Source;
use crate::compiler::parse::syntax::SyntaxNode;
use crate::compiler::parse::syntax::TokenKind;
use core::mem;
use rowan::{GreenNode, NodeOrToken};
use std::collections::HashMap;
type AsukaResult<T> = Result<T, AsukaError>;

const RECOVERY_SET: [TokenKind; 1] = [TokenKind::Newline];

pub(crate) struct Parser<'l, 't> {
    source: Source<'l, 't>,
    pub(crate) events: Vec<Event>,
    expected_kinds: Vec<TokenKind>,
    line: usize,
}

impl<'l, 't> Parser<'l, 't> {
    pub(crate) fn new(source: Source<'l, 't>) -> Self {
        Self {
            source,
            events: Vec::new(),
            expected_kinds: Vec::new(),
            line: 0,
        }
    }

    pub(crate) fn parse(mut self) -> Vec<Event> {
        grammar::root(&mut self);

        self.events
    }

    pub(crate) fn start_node(&mut self, kind: TokenKind) {
        self.events.push(Event::StartNode {
            kind,
            forward_parent: None,
            line: self.line,
        })
    }
    pub(crate) fn start_node_at(&mut self, checkpoint: usize, kind: TokenKind) {
        self.events.push(Event::StartNodeAt { kind, checkpoint })
    }

    pub(crate) fn finish_node(&mut self) {
        self.events.push(Event::FinishNode)
    }

    pub(crate) fn checkpoint(&mut self) -> usize {
        self.events.len()
    }

    pub(crate) fn bump(&mut self) {
        self.expected_kinds.clear();
        let token = self.source.next_token().unwrap();

        self.events.push(Event::AddToken {
            token_index: token.pos,
        });
    }

    pub(crate) fn peek(&mut self) -> Option<TokenKind> {
        self.source.peek_kind()
    }

    pub(crate) fn start(&mut self) -> Marker {
        let pos = self.events.len();
        self.events.push(Event::Placeholder);
        Marker::new(pos)
    }

    // pub(crate) fn abandon_curr_event(&mut self) {
    //     self.events.pop();
    // }

    pub(crate) fn expect(&mut self, kind: TokenKind) {
        if self.at(kind) {
            self.bump();
        } else {
            self.error();
        }
    }

    pub(crate) fn at(&mut self, kind: TokenKind) -> bool {
        self.expected_kinds.push(kind);
        self.peek() == Some(kind)
    }

    // pub(crate) fn skip(&mut self) {
    //     self.source.next_token().unwrap();
    // }

    // pub(crate) fn skip_until(&mut self, kind: TokenKind) {
    //     while !self.at(kind) {
    //         self.skip();
    //     }
    // }
    pub(crate) fn error(&mut self) {
        let current_token = self.source.peek_token();

        let (found, range) = if let Some(Token { kind, range, .. }) = current_token {
            (Some((*kind).into()), *range)
        } else {
            // If we’re at the end of the input we use the range of the very last token in the
            // input.
            (None, self.source.last_token_range().unwrap())
        };

        self.events.push(Event::Error(ParseError {
            expected: mem::take(&mut self.expected_kinds),
            found,
            range,
        }));

        // if !self.at_set(&RECOVERY_SET) && !self.at_end() {
        if !self.at_end() {
            let m = self.start();
            self.bump();
            m.complete(self, TokenKind::Error, self.line);
        }
    }

    pub(crate) fn at_set(&mut self, set: &[TokenKind]) -> bool {
        self.peek().map_or(false, |k| set.contains(&k))
    }

    pub(crate) fn at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    pub(crate) fn get_line(&self) -> usize {
        self.line
    }

    pub(crate) fn increment_line(&mut self) {
        self.line += 1;
    }
}

pub struct Parse {
    pub(crate) green_node: GreenNode,
    pub(crate) errors: Vec<ParseError>,
    pub token_index_map: Vec<usize>,
}
impl Parse {
    pub fn debug_tree(&self) -> String {
        let mut s = String::new();

        let syntax_node = SyntaxNode::new_root(self.green_node.clone());
        let tree = format!("{:#?}", syntax_node);

        // We cut off the last byte because formatting the SyntaxNode adds on a newline at the end.
        s.push_str(&tree[0..tree.len() - 1]);

        for error in &self.errors {
            s.push_str(&format!("\n{}", error));
        }

        s
    }

    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }

    pub fn make_token_map(&self) -> HashMap<SyntaxToken, usize> {
        let root_node = self.syntax();
        let mut map = HashMap::new();
        let mut token_count = 0;
        for element in root_node.descendants_with_tokens() {
            if let NodeOrToken::Token(tok) = element {
                let token_index = self.token_index_map[token_count];
                map.insert(tok, token_index);
                token_count += 1;
            }
        }
        map
    }
}

pub fn parse(input: &str) -> Parse {
    let tokens: Vec<_> = Lexer::new(input).collect();
    let source = Source::new(&tokens);
    let parser = Parser::new(source);
    let events = parser.parse();
    let sink = Sink::new(&tokens, events);
    sink.finish()
}

pub fn parse_save_tokens(input: &str) -> (Parse, Vec<Token>) {
    let tokens: Vec<_> = Lexer::new(input).collect();
    let source = Source::new(&tokens);
    let parser = Parser::new(source);
    let events = parser.parse();
    let sink = Sink::new(&tokens, events);
    (sink.finish(), tokens)
}

#[cfg(test)]
mod test {
    use crate::compiler::parse::parser::parse;
    use expect_test::expect;
    fn check(input: &str, expected_tree: expect_test::Expect) {
        let parse = parse(input);
        expected_tree.assert_eq(&parse.debug_tree());
    }

    // #[test]
    // fn parse_newline() {
    //     check("\n", expect![[r#"
    //     Root@0..1
    //         Newline@0..1 "\n"
    //     "#]]);
    // }
    #[test]
    fn parse_nothing() {
        check("", expect![[r#"Root@0..0"#]]);
    }

    #[test]
    fn parse_whitespace() {
        check(
            "   ",
            expect![[r#"
Root@0..3
  Whitespace@0..3 "   ""#]],
        );
    }
}

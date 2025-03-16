use super::{
    event::Event,
    parser::Parse,
    parser_error::ParseError,
    syntax::{AsukaLanguage, SyntaxToken},
};
use crate::compiler::parse::lexer::Token;
use rowan::{GreenNodeBuilder, Language};
use std::{collections::HashMap, mem};

pub(super) struct Sink<'l, 't> {
    builder: GreenNodeBuilder<'static>,
    tokens: &'l [Token<'t>],
    cursor: usize,
    events: Vec<Event>,
    errors: Vec<ParseError>,
    /// For each green token we add, store the original token index.
    token_index_map: Vec<usize>,
}

impl<'l, 't> Sink<'l, 't> {
    pub(super) fn new(tokens: &'l [Token<'t>], events: Vec<Event>) -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            tokens,
            cursor: 0,
            events,
            errors: Vec::new(),
            token_index_map: Vec::new(),
        }
    }

    pub(super) fn finish(mut self) -> Parse {
        for idx in 0..self.events.len() {
            match mem::replace(&mut self.events[idx], Event::Placeholder) {
                Event::AddToken { token_index } => {
                    self.token(token_index);
                }
                Event::StartNode {
                    kind,
                    forward_parent,
                    line,
                } => {
                    let mut kinds = vec![kind];

                    let mut idx = idx;
                    let mut forward_parent = forward_parent;

                    // Walk through the forward parent of the forward parent, and the forward parent
                    // of that, and of that, etc. until we reach a StartNode event without a forward
                    // parent.
                    while let Some(fp) = forward_parent {
                        idx += fp;

                        forward_parent = if let Event::StartNode {
                            kind,
                            forward_parent,
                            line,
                        } =
                            mem::replace(&mut self.events[idx], Event::Placeholder)
                        {
                            kinds.push(kind);
                            forward_parent
                        } else {
                            unreachable!()
                        };
                    }

                    for kind in kinds.into_iter().rev() {
                        self.builder.start_node(AsukaLanguage::kind_to_raw(kind));
                    }
                }
                Event::StartNodeAt {
                    kind: _,
                    checkpoint: _,
                } => unreachable!(),
                Event::FinishNode => self.builder.finish_node(),
                Event::Placeholder => {}
                Event::Error(error) => self.errors.push(error),
            }
            self.eat_trivial();
        }
        Parse {
            green_node: self.builder.finish(),
            errors: self.errors,
            token_index_map: self.token_index_map,
        }
    }

    fn eat_trivial(&mut self) {
        while let Some(token) = self.tokens.get(self.cursor) {
            if !token.kind.is_trivial() {
                break;
            }

            self.token(self.cursor);
        }
    }
    fn token(&mut self, token_index: usize) {
        let Token {
            kind,
            text,
            line,
            pos,
            ..
        } = self.tokens[self.cursor];
        self.builder
            .token(AsukaLanguage::kind_to_raw(kind), text.into());
        self.token_index_map.push(token_index);
        self.cursor += 1;
    }

    fn error(&mut self, err: ParseError) {
        todo!()
    }
}

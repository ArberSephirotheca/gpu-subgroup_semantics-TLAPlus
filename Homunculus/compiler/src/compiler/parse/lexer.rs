use crate::compiler::parse::syntax::TokenKind;
use logos::Logos;
use std::ops::Range as StdRange;
use text_size::{TextRange, TextSize};
// wrapper for logo's lexer, so we can get inner value of token
pub(crate) struct Lexer<'t> {
    inner: logos::Lexer<'t, TokenKind>,
    tokens_to_capture: Vec<Token<'t>>, // Store captured tokens
    inside_function: bool,
    line: usize,
    cursor: usize,
}

#[derive(Debug, PartialEq)]
pub struct Token<'t> {
    pub(crate) kind: TokenKind,
    pub(crate) text: &'t str,
    pub(crate) range: TextRange,
    pub(crate) line: usize,
    pub(crate) pos: usize,
}

impl<'t> Lexer<'t> {
    pub(crate) fn new(input: &'t str) -> Self {
        Self {
            inner: TokenKind::lexer(input),
            tokens_to_capture: Vec::new(),
            inside_function: false,
            // make it 5 to skip the version info
            line: 5,
            cursor: 0,
        }
    }

    pub fn line(&self) -> usize {
        self.line
    }
}

impl<'t> Iterator for Lexer<'t> {
    type Item = Token<'t>;

    fn next(&mut self) -> Option<Self::Item> {
        let kind = match self.inner.next()? {
            Ok(kind) => kind,
            Err(_) => panic!("Error: unexpected token at {:?}", self.inner.span()),
        };
        let text = self.inner.slice();
        let range = {
            let StdRange { start, end } = self.inner.span();
            let start = TextSize::try_from(start).unwrap();
            let end = TextSize::try_from(end).unwrap();

            TextRange::new(start, end)
        };
        if kind == TokenKind::Newline {
            self.line += 1;
        }
        self.cursor += 1;
        Some(Self::Item {
            kind,
            text,
            range,
            line: self.line,
            pos: self.cursor,
        })
    }

    // /// this function is called when we call next() on Lexer
    // /// it skips tokens that are not in the function call
    // fn next(&mut self) -> Option<Self::Item> {
    //     // If we have captured tokens, return them one-by-one
    //     if let Some(token) = self.tokens_to_capture.pop() {
    //         return Some(token);
    //     }

    //     // Continue lexing and capture tokens we're interested in
    //     'outer: loop {
    //         let kind = self.inner.next()?.expect("Error: lexer returned None");
    //         let text = self.inner.slice();
    //         let range = {
    //             let start = TextSize::try_from(self.inner.span().start).unwrap();
    //             let end = TextSize::try_from(self.inner.span().end).unwrap();
    //             TextRange::new(start, end)
    //         };

    //         match kind {
    //             TokenKind::OpDecorate => {
    //                 // Start capturing the entire instruction
    //                 let mut capture_instruction = vec![Token { kind, text, range }];
    //                 let mut contains_builtin = false;
    //                 self.tokens_to_capture.push(Token { kind, text, range });

    //                 // Continue capturing until we hit a newline or end of input
    //                 'inner: loop  {
    //                     let next_token = self.inner.next()?.expect("Error: lexer returned None");
    //                     let next_text = self.inner.slice();
    //                     let next_range = {
    //                         let start = TextSize::try_from(self.inner.span().start).unwrap();
    //                         let end = TextSize::try_from(self.inner.span().end).unwrap();
    //                         TextRange::new(start, end)
    //                     };

    //                     // Capture each argument token until we hit a newline
    //                     if next_token == TokenKind::Newline {
    //                         break 'inner; // Stop capturing at newline
    //                     }
    //                     if next_token == TokenKind::BuiltIn {
    //                         contains_builtin = true;  // Set flag if BuiltIn is found
    //                     }
    //                     capture_instruction.push(Token { kind: next_token, text: next_text, range: next_range });
    //                 }
    //                 // Only keep the instruction if it contains "BuiltIn"
    //                 if contains_builtin {
    //                     self.tokens_to_capture.extend(capture_instruction);
    //                 }
    //             },

    //             TokenKind::OpFunction => {
    //                 // Start capturing the entire function
    //                 self.tokens_to_capture.push(Token { kind, text, range });
    //                 self.inside_function = true;

    //             },
    //             // Handle OpFunctionEnd and other tokens
    //             TokenKind::OpFunctionEnd => {
    //                 if self.inside_function {
    //                     self.tokens_to_capture.push(Token { kind, text, range });
    //                     self.inside_function = false;
    //                 }
    //             }
    //             _ if self.inside_function => {
    //                 // Capture tokens inside the function as before
    //                 self.tokens_to_capture.push(Token { kind, text, range });
    //             }
    //             _ => break 'outer, // Skip tokens outside of functions
    //         }
    //     }

    //     // Return the next captured token if any, or continue lexing
    //     self.tokens_to_capture.pop()
    // }
}

mod test {}

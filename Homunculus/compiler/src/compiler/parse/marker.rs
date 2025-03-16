use super::{event::Event, parser::Parser, syntax::TokenKind};

pub struct Marker {
    pos: usize,
    completed: bool,
}

impl Marker {
    pub(super) fn new(pos: usize) -> Self {
        Self {
            pos,
            completed: false,
        }
    }

    pub(super) fn complete(
        mut self,
        p: &mut Parser,
        kind: TokenKind,
        line: usize,
    ) -> CompletedMarker {
        self.completed = true;
        let event_at_pos = &mut p.events[self.pos];
        assert_eq!(*event_at_pos, Event::Placeholder);

        *event_at_pos = Event::StartNode {
            kind,
            forward_parent: None,
            line,
        };

        p.events.push(Event::FinishNode);

        CompletedMarker {
            pos: self.pos,
            line,
        }
    }
}

impl Drop for Marker {
    fn drop(&mut self) {
        if !self.completed {
            panic!("Marker need to be completed!");
        }
    }
}

pub(crate) struct CompletedMarker {
    pos: usize,
    line: usize,
}

impl CompletedMarker {
    pub(super) fn precede(&self, p: &mut Parser) -> Marker {
        let new_m = p.start();

        if let Event::StartNode {
            ref mut forward_parent,
            ..
        } = p.events[self.pos]
        {
            *forward_parent = Some(new_m.pos - self.pos);
        } else {
            unreachable!();
        }
        new_m
    }
}

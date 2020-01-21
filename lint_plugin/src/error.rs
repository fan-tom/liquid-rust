use syntax_pos::Span;

pub struct TypeError {
    pub description: String,
    pub span: Option<Span>,
}

impl TypeError {
    pub fn new(description: String, span: impl Into<Option<Span>>) -> Self {
        Self {
            description,
            span: span.into(),
        }
    }
}
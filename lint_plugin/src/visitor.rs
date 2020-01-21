pub trait Visitor<'e, T>
    where T: Visitable
{
    fn visit(&mut self, expr: &'e T) {}
}

impl<'e, F: FnMut(&'e T), T: Visitable + 'e> Visitor<'e, T> for F {
    fn visit(&mut self, expr: &'e T) {
        self(expr)
    }
}

pub trait Visitable: Sized {
    fn accept<'s>(&'s self, v: &mut impl Visitor<'s, Self>);
}

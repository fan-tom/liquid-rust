pub trait Folder<T>
{
    fn fold(&mut self, expr: T) -> T;
}

impl<'e, T, F: FnMut(T) -> T> Folder<T> for F {
    fn fold(&mut self, expr: T) -> T {
        self(expr)
    }
}

pub trait Foldable<T = Self>: Sized {
    fn accept<'s>(self, v: &mut impl Folder<T>) -> Self;
}

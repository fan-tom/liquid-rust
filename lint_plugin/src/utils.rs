use itertools::Either;

pub const ANN_RET_NAME: &str = "return";

pub trait IntoEither: Sized {
    fn into_left<R>(self) -> Either<Self, R> {
        Either::Left(self)
    }
    fn into_right<L>(self) -> Either<L, Self> {
        Either::Right(self)
    }
}

impl<T> IntoEither for T {}
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

pub trait IntoFish: Sized {
    // Bound to Into instead of From, as it is more universal.
    // If you have From<S> for T, you automatically have Into<T> for S,
    // but you may write Into<T> for S without having From<S> for T, so having From implies Into, but not vice versa
    fn to<U>(self) -> U where Self: Into<U> {
        self.into()
    }
}

impl<T> IntoFish for T {}

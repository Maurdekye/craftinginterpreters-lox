use std::{error::Error as StdError, fmt::Display, vec};

pub struct Peekable<I: Iterator> {
    iter: I,
    slot: Option<I::Item>,
}

impl<I: Iterator> Peekable<I> {
    pub fn new(mut iter: I) -> Self {
        let slot = iter.next();
        Self { iter, slot }
    }

    /// Observe the next item in the iterator
    /// without consuming it
    pub fn peek(&self) -> Option<&I::Item> {
        self.slot.as_ref()
    }

    /// Advance the iterator, retrieving the next item, but
    /// only if it matches a given predicate. Return None
    /// otherwise, leaving the iterator untouched.
    pub fn next_if(&mut self, pred: impl FnOnce(&I::Item) -> bool) -> Option<I::Item> {
        self.slot
            .as_ref()
            .is_some_and(pred)
            .then(|| self.next())
            .flatten()
    }
}

impl<I: Iterator> Peekable<Peekable<I>> {
    pub fn new_double(iter: I) -> Self {
        Self::new(Peekable::<I>::new(iter))
    }

    /// Observe the next-next item in the iterator
    /// without consuming it (the item after the next item)
    pub fn peek_second(&self) -> Option<&I::Item> {
        self.iter.slot.as_ref()
    }
}

impl<I: Iterator> Iterator for Peekable<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        std::mem::replace(&mut self.slot, self.iter.next())
    }
}

#[derive(Clone, Debug)]
pub struct Location {
    pub line: usize,
    pub character: usize,
}

impl Locateable for Location {
    fn line(&self) -> usize {
        self.line
    }

    fn character(&self) -> usize {
        self.character
    }
}

impl<L: Locateable> From<&L> for Location {
    fn from(value: &L) -> Self {
        Location {
            line: value.line(),
            character: value.character(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Located<T> {
    pub line: usize,
    pub character: usize,
    pub item: T,
}

impl<T: Display> Display for Located<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}:{}] {}", self.line, self.character, self.item)
    }
}

impl<T: StdError> StdError for Located<T> {}

pub trait Locateable {
    fn line(&self) -> usize;
    fn character(&self) -> usize;
}

impl<T> Locateable for Located<T> {
    fn line(&self) -> usize {
        self.line
    }

    fn character(&self) -> usize {
        self.character
    }
}

pub trait LocatedAt: Sized {
    fn at(self, locator: &impl Locateable) -> Located<Self> {
        Located {
            line: locator.line(),
            character: locator.character(),
            item: self,
        }
    }
}

impl<T> LocatedAt for T {}

#[derive(Clone, Debug)]
pub enum MaybeLocated<T> {
    Located(Located<T>),
    Unlocated(T),
}

impl<T: Display> Display for MaybeLocated<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeLocated::Located(located) => write!(f, "{located}"),
            MaybeLocated::Unlocated(unlocated) => write!(f, "{unlocated}"),
        }
    }
}

impl<T: StdError> StdError for MaybeLocated<T> {}

pub trait MaybeLocatedAt: Sized {
    fn unlocated(self) -> MaybeLocated<Self> {
        MaybeLocated::Unlocated(self)
    }

    fn located_at(self, locateable: &impl Locateable) -> MaybeLocated<Self> {
        MaybeLocated::Located(self.at(locateable))
    }

    fn located_if(self, some_locateable: Option<&impl Locateable>) -> MaybeLocated<Self> {
        match some_locateable {
            Some(locateable) => self.located_at(locateable),
            None => self.unlocated(),
        }
    }
}

impl<T> MaybeLocatedAt for T {}

#[derive(Clone, Debug)]
pub struct Errors<E>(Vec<E>);

impl<E> Errors<E> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, error: impl Into<E>) {
        self.0.push(error.into());
    }

    /// If there are no errors, return an Ok with the passed value
    pub fn empty_ok<T>(self, ok: T) -> Result<T, Self> {
        self.0.is_empty().then_some(ok).ok_or(self)
    }

    #[allow(unused)]
    pub fn map<F, O>(self, f: F) -> Errors<O>
    where
        F: FnMut(E) -> O,
    {
        Errors(self.0.into_iter().map(f).collect())
    }
}

pub trait ErrorsInto<E, T> {
    /// Extract the errors from a result and push them into an
    /// Errors collection, then transform the result into an Option
    fn errors_into(self, errors: &mut Errors<E>) -> Option<T>;
}

impl<E, U: Into<E>, T> ErrorsInto<E, T> for Result<T, Errors<U>> {
    fn errors_into(self, errors: &mut Errors<E>) -> Option<T> {
        match self {
            Ok(value) => Some(value),
            Err(new_errors) => {
                errors.extend(new_errors);
                None
            }
        }
    }
}

impl<E> From<Vec<E>> for Errors<E> {
    fn from(value: Vec<E>) -> Self {
        Errors(value)
    }
}

impl<E, U: Into<E>> FromIterator<U> for Errors<E> {
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        Errors(iter.into_iter().map(Into::<E>::into).collect())
    }
}

impl<E> IntoIterator for Errors<E> {
    type Item = E;
    type IntoIter = vec::IntoIter<E>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<E, U: Into<E>> Extend<U> for Errors<E> {
    fn extend<T: IntoIterator<Item = U>>(&mut self, iter: T) {
        self.0.extend(iter.into_iter().map(Into::<E>::into));
    }
}

impl<E: Display> Display for Errors<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for err in &self.0 {
            writeln!(f, "{err}")?;
        }
        Ok(())
    }
}

impl<E, T: Default> Into<Result<T, Errors<E>>> for Errors<E> {
    fn into(self) -> Result<T, Errors<E>> {
        self.empty_ok(T::default())
    }
}

impl<E: StdError> StdError for Errors<E> {}

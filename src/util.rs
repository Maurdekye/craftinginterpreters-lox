use std::{
    borrow::Cow,
    collections::hash_map::Entry,
    error::Error as StdError,
    fmt::Display,
    iter::once,
    process::{ExitCode, Termination},
    vec,
};

use crate::interpreter::{MaybeWithSignal, Signal};

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

#[derive(Clone, Debug, std::hash::Hash, PartialEq, Eq)]
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

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}:{}]", self.line, self.character)
    }
}

#[derive(Clone, Debug)]
pub struct Located<T> {
    pub line: usize,
    pub character: usize,
    pub item: T,
}

impl<T> Located<T> {
    pub fn map<V>(self, f: impl FnOnce(T) -> V) -> Located<V> {
        Located {
            line: self.line,
            character: self.character,
            item: f(self.item),
        }
    }

    pub fn split(self) -> (T, Location) {
        let Located {
            line,
            character,
            item,
        } = self;
        (item, Location { line, character })
    }
}

impl<T> Located<Box<T>> {
    pub fn as_deref(self) -> Located<T> {
        self.map(|x| *x)
    }
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

    fn location(&self) -> Location
    where
        Self: Sized,
    {
        self.into()
    }
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
    fn at(self, locateable: &impl Locateable) -> Located<Self> {
        Located {
            line: locateable.line(),
            character: locateable.character(),
            item: self,
        }
    }
}

impl<T> LocatedAt for T {}

pub trait AppendLocatedError<F, U, E, T> {
    type Output;

    fn with_err_at(self, err_factory: F, locateable: &impl Locateable) -> Self::Output;
}

impl<V, F, U, E, T> AppendLocatedError<F, U, E, T> for Result<V, E>
where
    U: From<E>,
    F: FnOnce(U) -> T,
{
    type Output = Result<V, Located<T>>;

    fn with_err_at(self, err_factory: F, locateable: &impl Locateable) -> Self::Output {
        self.map_err(|err| err_factory(err.into()).at(locateable))
    }
}

/// another duped trait... wish specialization would come soon
pub trait AppendLocatedErrorWithSignal<F, U, E, T> {
    type Output;

    fn with_maybe_signaled_err_at(
        self,
        err_factory: F,
        locateable: &impl Locateable,
    ) -> Self::Output;
}

impl<V, F, U, E, T> AppendLocatedErrorWithSignal<F, U, E, T> for Result<V, MaybeWithSignal<E>>
where
    U: From<E>,
    F: FnOnce(U) -> T,
{
    type Output = Result<V, MaybeWithSignal<Located<T>>>;

    fn with_maybe_signaled_err_at(
        self,
        err_factory: F,
        locateable: &impl Locateable,
    ) -> Self::Output {
        self.map_err(|err| err.map(|err| err_factory(err.into()).at(locateable)))
    }
}

pub trait AppendMaybeLocatedError<F, U, E, T> {
    type Output;

    fn with_err_located_if(
        self,
        err_factory: F,
        locateable: Option<&impl Locateable>,
    ) -> Self::Output;

    fn with_err_located_at(self, err_factory: F, locateable: &impl Locateable) -> Self::Output
    where
        Self: Sized,
    {
        self.with_err_located_if(err_factory, Some(locateable))
    }

    fn with_err_unlocated<L: Locateable>(self, err_factory: F) -> Self::Output
    where
        Self: Sized,
    {
        self.with_err_located_if(err_factory, <Option<&L>>::None)
    }
}

impl<V, F, U, E, T> AppendMaybeLocatedError<F, U, E, T> for Result<V, E>
where
    U: From<E>,
    F: FnOnce(U) -> T,
{
    type Output = Result<V, MaybeLocated<T>>;

    fn with_err_located_if(
        self,
        err_factory: F,
        locateable: Option<&impl Locateable>,
    ) -> Self::Output {
        self.map_err(|err| err_factory(err.into()).located_if(locateable))
    }
}

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

impl<E> From<E> for Errors<E> {
    fn from(value: E) -> Self {
        once(value).collect()
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

pub trait ErrorInto<E, T> {
    /// Extract the error from a result and push it into an
    /// Errors collection, then transform the result into an Option
    fn error_into(self, errors: &mut Errors<E>) -> Option<T>;
}

impl<E, U: Into<E>, T> ErrorInto<E, T> for Result<T, U> {
    fn error_into(self, errors: &mut Errors<E>) -> Option<T> {
        match self {
            Ok(value) => Some(value),
            Err(new_error) => {
                errors.push(new_error);
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
        let mut errs_iter = self.0.iter();
        if let Some(err) = errs_iter.next() {
            write!(f, "{err}")?;
            for err in errs_iter {
                write!(f, "\n{err}")?;
            }
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

impl<E: Termination> Termination for Errors<E> {
    fn report(self) -> std::process::ExitCode {
        match self.into_iter().next() {
            Some(e) => e.report(),
            None => ExitCode::SUCCESS,
        }
    }
}

pub trait WrapErrors {
    type Output;

    fn errs(self) -> Self::Output;
}

impl<T, E> WrapErrors for Result<T, E> {
    type Output = Result<T, Errors<E>>;

    fn errs(self) -> Self::Output {
        self.map_err(|err| once(err).collect())
    }
}

pub trait EntryInsert<V> {
    fn insert(self, value: V);
}

impl<K, V> EntryInsert<V> for Entry<'_, K, V> {
    fn insert(self, value: V) {
        match self {
            Entry::Occupied(mut entry) => {
                entry.insert(value);
            }
            Entry::Vacant(entry) => {
                entry.insert(value);
            }
        }
    }
}

pub trait AsOwned<'a> {
    type Output;

    fn as_owned(self) -> Self::Output;
}

impl<'a, T: Clone + 'a, E> AsOwned<'a> for Result<T, E> {
    type Output = Result<Cow<'a, T>, E>;

    fn as_owned(self) -> Self::Output {
        self.map(|v| Cow::Owned(v))
    }
}

pub trait Signaling: Sized {
    fn signaling(self, signal: Signal) -> MaybeWithSignal<Self> {
        MaybeWithSignal::WithSignal(self, signal)
    }

    fn no_signal(self) -> MaybeWithSignal<Self> {
        MaybeWithSignal::NoSignal(self)
    }
}

impl<T: Sized> Signaling for T {}

pub trait SignalingResult {
    type SignalingOutput;
    type NotSignalingOutput;

    fn err_signaling(self, signal: Signal) -> Self::SignalingOutput;
    fn err_no_signal(self) -> Self::NotSignalingOutput;
}

impl<T, E: Sized> SignalingResult for Result<T, E> {
    type SignalingOutput = Result<T, MaybeWithSignal<E>>;
    type NotSignalingOutput = Result<T, MaybeWithSignal<E>>;

    fn err_signaling(self, signal: Signal) -> Self::SignalingOutput {
        self.map_err(|e| e.signaling(signal))
    }

    fn err_no_signal(self) -> Self::NotSignalingOutput {
        self.map_err(Signaling::no_signal)
    }
}

pub struct Indented<'a, T>(&'a T, usize)
where
    T: ?Sized;

impl<'a, T> Display for Indented<'a, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let lines = format!("{}", self.0);
        let indent = " ".repeat(self.1);
        for line in lines.split("\n") {
            writeln!(f, "{indent}{line}")?;
        }
        Ok(())
    }
}

pub trait Indent: Display {
    fn indented(&self, indent: usize) -> Indented<Self> {
        Indented(self, indent)
    }
}

impl<T> Indent for T where T: Display {}

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
    pub fn next_if(&mut self, pred: impl FnOnce(&I::Item) -> bool) -> Option<I::Item>
    {
        self.slot.as_ref().is_some_and(pred).then(|| self.next()).flatten()
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

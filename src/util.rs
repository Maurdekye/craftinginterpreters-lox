pub struct Peekable<I: Iterator> {
    iter: I,
    slot: Option<I::Item>,
}

impl<I: Iterator> Peekable<I> {
    pub fn new(mut iter: I) -> Self {
        let slot = iter.next();
        Self { iter, slot }
    }

    pub fn peek(&self) -> Option<&I::Item> {
        self.slot.as_ref()
    }
}

impl<'a, I: Iterator> Peekable<Peekable<I>> {
    pub fn new_double(iter: I) -> Self {
        Self::new(Peekable::<I>::new(iter))
    }

    pub fn peek_second(&self) -> Option<&I::Item> {
        self.iter.slot.as_ref()
    }
}

impl<'a, I: Iterator> Iterator for Peekable<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        std::mem::replace(&mut self.slot, self.iter.next())
    }
}

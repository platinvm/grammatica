use std::hash::Hash;
use std::ops::Deref;

#[derive(Debug, Clone, Eq)]
pub struct Terminal<T: Clone + Eq + Hash>(pub T);

impl<T: Clone + Eq + Hash> Deref for Terminal<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone + Eq + Hash> PartialEq for Terminal<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Clone + Eq + Hash> Hash for Terminal<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Symbol<T: Clone + Eq + Hash> {
    Terminal(T),
    NonTerminal(String),
}

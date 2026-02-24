use rpds::ListSync;
use std::fmt;
use std::hash::{Hash, Hasher};

/// A persistent, immutable singly-linked list backed by `rpds::ListSync`.
///
/// Thread-safe (Send + Sync) via Arc-based structural sharing.
///
/// # Examples
/// ```
/// use functype_core::list;
/// use functype_core::collections::list::List;
///
/// let l = list![1, 2, 3];
/// assert_eq!(l.head(), Some(&1));
/// assert_eq!(l.len(), 3);
///
/// let l2 = l.prepend(0);
/// assert_eq!(l2.len(), 4);
/// assert_eq!(l.len(), 3); // original unchanged
/// ```
#[derive(Clone)]
pub struct List<T: Clone>(ListSync<T>);

impl<T: Clone> List<T> {
    /// Creates an empty list.
    pub fn new() -> Self {
        List(ListSync::new_sync())
    }

    /// Creates a list from an iterator.
    pub fn of(iter: impl IntoIterator<Item = T>) -> Self {
        let items: Vec<T> = iter.into_iter().collect();
        let mut list = ListSync::new_sync();
        for item in items.into_iter().rev() {
            list = list.push_front(item);
        }
        List(list)
    }

    /// Prepends an element to the front of the list. Alias for `cons`.
    pub fn prepend(&self, value: T) -> Self {
        List(self.0.push_front(value))
    }

    /// Prepends an element to the front. Same as `prepend`.
    pub fn cons(&self, value: T) -> Self {
        self.prepend(value)
    }

    /// Returns a reference to the first element, or `None` if empty.
    pub fn head(&self) -> Option<&T> {
        self.0.first()
    }

    /// Returns the list without its first element, or `None` if empty.
    pub fn tail(&self) -> Option<List<T>> {
        self.0.drop_first().map(List)
    }

    /// Returns `true` if the list has no elements.
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    /// Returns the number of elements.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Maps a function over all elements, returning a new list.
    pub fn map<U: Clone, F: Fn(&T) -> U>(&self, f: F) -> List<U> {
        List::of(self.0.iter().map(f))
    }

    /// Maps a function that returns a list over all elements, then flattens.
    pub fn flat_map<U: Clone, F: Fn(&T) -> List<U>>(&self, f: F) -> List<U> {
        let items: Vec<U> = self.0.iter().flat_map(|item| f(item).to_vec()).collect();
        List::of(items)
    }

    /// Returns a new list containing only elements that satisfy the predicate.
    pub fn filter<F: Fn(&T) -> bool>(&self, f: F) -> List<T> {
        List::of(self.0.iter().filter(|item| f(item)).cloned())
    }

    /// Folds the list from left to right.
    pub fn fold<U, F: Fn(U, &T) -> U>(&self, init: U, f: F) -> U {
        self.0.iter().fold(init, f)
    }

    /// Converts the list to a `Vec`.
    pub fn to_vec(&self) -> Vec<T> {
        self.0.iter().cloned().collect()
    }

    /// Returns an iterator over references to elements.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }
}

impl<T: Clone> Default for List<T> {
    fn default() -> Self {
        List::new()
    }
}

impl<T: Clone + PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.0.iter().zip(other.0.iter()).all(|(a, b)| a == b)
    }
}

impl<T: Clone + Eq> Eq for List<T> {}

impl<T: Clone + Hash> Hash for List<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for item in self.0.iter() {
            item.hash(state);
        }
    }
}

impl<T: Clone + fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl<T: Clone + fmt::Display> fmt::Display for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "List(")?;
        let mut first = true;
        for item in self.0.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", item)?;
            first = false;
        }
        write!(f, ")")
    }
}

impl<T: Clone> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_vec().into_iter()
    }
}

impl<T: Clone> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        List::of(iter)
    }
}

/// Creates a `List` from a list of elements.
///
/// # Examples
/// ```
/// use functype_core::list;
///
/// let empty: functype_core::collections::list::List<i32> = list![];
/// assert!(empty.is_empty());
///
/// let l = list![1, 2, 3];
/// assert_eq!(l.len(), 3);
/// ```
#[macro_export]
macro_rules! list {
    [] => {
        $crate::collections::list::List::new()
    };
    [$($elem:expr),+ $(,)?] => {
        $crate::collections::list::List::of(vec![$($elem),+])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_creates_empty() {
        let l: List<i32> = List::new();
        assert!(l.is_empty());
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn of_creates_from_iter() {
        let l = List::of(vec![1, 2, 3]);
        assert_eq!(l.len(), 3);
        assert_eq!(l.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn prepend_adds_to_front() {
        let l = List::of(vec![2, 3]);
        let l2 = l.prepend(1);
        assert_eq!(l2.to_vec(), vec![1, 2, 3]);
        assert_eq!(l.to_vec(), vec![2, 3]); // original unchanged
    }

    #[test]
    fn cons_is_prepend() {
        let l = List::of(vec![2, 3]);
        assert_eq!(l.cons(1).to_vec(), l.prepend(1).to_vec());
    }

    #[test]
    fn head_returns_first() {
        let l = list![1, 2, 3];
        assert_eq!(l.head(), Some(&1));
    }

    #[test]
    fn head_empty_is_none() {
        let l: List<i32> = list![];
        assert_eq!(l.head(), None);
    }

    #[test]
    fn tail_returns_rest() {
        let l = list![1, 2, 3];
        let t = l.tail().unwrap();
        assert_eq!(t.to_vec(), vec![2, 3]);
    }

    #[test]
    fn tail_empty_is_none() {
        let l: List<i32> = list![];
        assert!(l.tail().is_none());
    }

    #[test]
    fn tail_single_element() {
        let l = list![1];
        let t = l.tail().unwrap();
        assert!(t.is_empty());
    }

    #[test]
    fn map_transforms_elements() {
        let l = list![1, 2, 3];
        let mapped = l.map(|x| x * 2);
        assert_eq!(mapped.to_vec(), vec![2, 4, 6]);
    }

    #[test]
    fn flat_map_flattens() {
        let l = list![1, 2, 3];
        let result = l.flat_map(|x| list![*x, x * 10]);
        assert_eq!(result.to_vec(), vec![1, 10, 2, 20, 3, 30]);
    }

    #[test]
    fn filter_removes_elements() {
        let l = list![1, 2, 3, 4, 5];
        let filtered = l.filter(|x| *x % 2 == 0);
        assert_eq!(filtered.to_vec(), vec![2, 4]);
    }

    #[test]
    fn fold_accumulates() {
        let l = list![1, 2, 3, 4];
        let sum = l.fold(0, |acc, x| acc + x);
        assert_eq!(sum, 10);
    }

    #[test]
    fn equality() {
        let a = list![1, 2, 3];
        let b = list![1, 2, 3];
        let c = list![1, 2, 4];
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn display_formatting() {
        let l = list![1, 2, 3];
        assert_eq!(format!("{}", l), "List(1, 2, 3)");

        let empty: List<i32> = list![];
        assert_eq!(format!("{}", empty), "List()");
    }

    #[test]
    fn from_iterator() {
        let l: List<i32> = (1..=3).collect();
        assert_eq!(l.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn into_iter_works() {
        let l = list![1, 2, 3];
        let v: Vec<i32> = l.into_iter().collect();
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn list_macro_empty() {
        let l: List<i32> = list![];
        assert!(l.is_empty());
    }

    #[test]
    fn list_macro_elements() {
        let l = list![1, 2, 3];
        assert_eq!(l.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn list_macro_trailing_comma() {
        let l = list![1, 2, 3,];
        assert_eq!(l.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn structural_sharing() {
        let l1 = list![2, 3];
        let l2 = l1.prepend(1);
        assert_eq!(l1.len(), 2);
        assert_eq!(l2.len(), 3);
        assert_eq!(l2.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn default_is_empty() {
        let l: List<i32> = List::default();
        assert!(l.is_empty());
    }
}

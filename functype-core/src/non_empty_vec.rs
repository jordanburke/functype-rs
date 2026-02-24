use std::fmt;
use std::hash::{Hash, Hasher};

/// A vector guaranteed to contain at least one element.
///
/// `NonEmptyVec<T>` provides a type-level guarantee that the collection is never empty,
/// eliminating the need for runtime checks when accessing the first element.
///
/// # Examples
/// ```
/// use functype_core::non_empty_vec::NonEmptyVec;
/// use functype_core::nev;
///
/// let v = nev![1, 2, 3];
/// assert_eq!(*v.head(), 1);
/// assert_eq!(v.len(), 3);
/// ```
#[derive(Clone)]
pub struct NonEmptyVec<T> {
    head: T,
    tail: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    /// Creates a new `NonEmptyVec` with a single element.
    pub fn new(head: T) -> Self {
        NonEmptyVec {
            head,
            tail: Vec::new(),
        }
    }

    /// Creates a `NonEmptyVec` from a head element and a tail vector.
    pub fn of(head: T, tail: Vec<T>) -> Self {
        NonEmptyVec { head, tail }
    }

    /// Attempts to create a `NonEmptyVec` from a `Vec`.
    /// Returns `None` if the vector is empty.
    pub fn from_vec(mut vec: Vec<T>) -> Option<Self> {
        if vec.is_empty() {
            None
        } else {
            let head = vec.remove(0);
            Some(NonEmptyVec { head, tail: vec })
        }
    }

    /// Creates a `NonEmptyVec` from a `Vec` without checking that it's non-empty.
    ///
    /// # Panics
    /// Panics if the vector is empty.
    pub fn from_vec_unchecked(mut vec: Vec<T>) -> Self {
        assert!(!vec.is_empty(), "NonEmptyVec::from_vec_unchecked called with empty vec");
        let head = vec.remove(0);
        NonEmptyVec { head, tail: vec }
    }

    /// Returns a reference to the first element.
    pub fn head(&self) -> &T {
        &self.head
    }

    /// Returns a slice of all elements after the first.
    pub fn tail(&self) -> &[T] {
        &self.tail
    }

    /// Returns a reference to the last element.
    pub fn last(&self) -> &T {
        self.tail.last().unwrap_or(&self.head)
    }

    /// Returns the number of elements.
    pub fn len(&self) -> usize {
        1 + self.tail.len()
    }

    /// Converts into a `Vec<T>`.
    pub fn into_vec(self) -> Vec<T> {
        let mut v = Vec::with_capacity(self.len());
        v.push(self.head);
        v.extend(self.tail);
        v
    }

    /// Returns a new `Vec<T>` containing all elements.
    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        let mut v = Vec::with_capacity(self.len());
        v.push(self.head.clone());
        v.extend(self.tail.iter().cloned());
        v
    }

    /// Returns a slice view of all elements.
    ///
    /// Note: This allocates a temporary Vec. For iteration, prefer `iter()`.
    pub fn as_slice(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.to_vec()
    }

    /// Applies a function to each element, returning a new `NonEmptyVec`.
    pub fn map<U, F: Fn(&T) -> U>(&self, f: F) -> NonEmptyVec<U> {
        NonEmptyVec {
            head: f(&self.head),
            tail: self.tail.iter().map(f).collect(),
        }
    }

    /// Applies a function that returns a `NonEmptyVec` to each element, then flattens.
    pub fn flat_map<U, F: Fn(&T) -> NonEmptyVec<U>>(&self, f: F) -> NonEmptyVec<U> {
        let first = f(&self.head);
        let mut result_tail = first.tail;
        for item in &self.tail {
            let mapped = f(item);
            result_tail.push(mapped.head);
            result_tail.extend(mapped.tail);
        }
        NonEmptyVec {
            head: first.head,
            tail: result_tail,
        }
    }

    /// Returns a new `NonEmptyVec` with the element appended.
    pub fn push(&self, value: T) -> NonEmptyVec<T>
    where
        T: Clone,
    {
        let mut new_tail = self.tail.clone();
        new_tail.push(value);
        NonEmptyVec {
            head: self.head.clone(),
            tail: new_tail,
        }
    }

    /// Appends an element in place.
    pub fn push_mut(&mut self, value: T) {
        self.tail.push(value);
    }

    /// Returns a new `NonEmptyVec` with all elements from `other` appended.
    pub fn append(&self, other: &NonEmptyVec<T>) -> NonEmptyVec<T>
    where
        T: Clone,
    {
        let mut new_tail = self.tail.clone();
        new_tail.push(other.head.clone());
        new_tail.extend(other.tail.iter().cloned());
        NonEmptyVec {
            head: self.head.clone(),
            tail: new_tail,
        }
    }

    /// Folds the elements using an initial value and a combining function.
    pub fn fold<U, F: Fn(U, &T) -> U>(&self, init: U, f: F) -> U {
        let acc = f(init, &self.head);
        self.tail.iter().fold(acc, f)
    }

    /// Reduces the elements using a combining function.
    /// Unlike `fold`, this uses the first element as the initial accumulator.
    pub fn reduce<F: Fn(&T, &T) -> T>(&self, f: F) -> T
    where
        T: Clone,
    {
        self.tail.iter().fold(self.head.clone(), |acc, item| f(&acc, item))
    }

    /// Returns an iterator over references to all elements.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: Some(&self.head),
            tail: self.tail.iter(),
        }
    }

    /// Returns `true` if the `NonEmptyVec` contains the given value.
    pub fn contains(&self, value: &T) -> bool
    where
        T: PartialEq,
    {
        self.head == *value || self.tail.contains(value)
    }

    /// Returns a reference to the first element matching the predicate.
    pub fn find<F: Fn(&T) -> bool>(&self, f: F) -> Option<&T> {
        if f(&self.head) {
            Some(&self.head)
        } else {
            self.tail.iter().find(|item| f(item))
        }
    }

    /// Zips two `NonEmptyVec`s together, truncating to the shorter length.
    pub fn zip<'a, U>(&'a self, other: &'a NonEmptyVec<U>) -> NonEmptyVec<(&'a T, &'a U)> {
        let head = (&self.head, &other.head);
        let tail: Vec<(&T, &U)> = self.tail.iter().zip(other.tail.iter()).collect();
        NonEmptyVec { head, tail }
    }
}

/// Iterator over references to elements of a `NonEmptyVec`.
pub struct Iter<'a, T> {
    head: Option<&'a T>,
    tail: std::slice::Iter<'a, T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.take().or_else(|| self.tail.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = if self.head.is_some() { 1 } else { 0 } + self.tail.len();
        (remaining, Some(remaining))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

/// Owning iterator over elements of a `NonEmptyVec`.
pub struct IntoIter<T> {
    head: Option<T>,
    tail: std::vec::IntoIter<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.take().or_else(|| self.tail.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = if self.head.is_some() { 1 } else { 0 } + self.tail.len();
        (remaining, Some(remaining))
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> IntoIterator for NonEmptyVec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            head: Some(self.head),
            tail: self.tail.into_iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: fmt::Debug> fmt::Debug for NonEmptyVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: fmt::Display> fmt::Display for NonEmptyVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        write!(f, "{}", self.head)?;
        for item in &self.tail {
            write!(f, ", {}", item)?;
        }
        write!(f, "]")
    }
}

impl<T: PartialEq> PartialEq for NonEmptyVec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.tail == other.tail
    }
}

impl<T: Eq> Eq for NonEmptyVec<T> {}

impl<T: Hash> Hash for NonEmptyVec<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.head.hash(state);
        self.tail.hash(state);
    }
}

/// Creates a `NonEmptyVec` from a list of elements.
///
/// # Examples
/// ```
/// use functype_core::nev;
///
/// let v = nev![42];
/// assert_eq!(v.len(), 1);
///
/// let v = nev![1, 2, 3];
/// assert_eq!(v.len(), 3);
/// ```
#[macro_export]
macro_rules! nev {
    ($head:expr $(, $tail:expr)* $(,)?) => {
        $crate::non_empty_vec::NonEmptyVec::of($head, vec![$($tail),*])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_creates_single_element() {
        let v = NonEmptyVec::new(42);
        assert_eq!(*v.head(), 42);
        assert_eq!(v.len(), 1);
        assert!(v.tail().is_empty());
    }

    #[test]
    fn of_creates_with_head_and_tail() {
        let v = NonEmptyVec::of(1, vec![2, 3]);
        assert_eq!(*v.head(), 1);
        assert_eq!(v.tail(), &[2, 3]);
        assert_eq!(v.len(), 3);
    }

    #[test]
    fn from_vec_empty_returns_none() {
        let result = NonEmptyVec::<i32>::from_vec(vec![]);
        assert!(result.is_none());
    }

    #[test]
    fn from_vec_non_empty_returns_some() {
        let v = NonEmptyVec::from_vec(vec![1, 2, 3]).unwrap();
        assert_eq!(*v.head(), 1);
        assert_eq!(v.tail(), &[2, 3]);
    }

    #[test]
    fn from_vec_roundtrip() {
        let original = vec![1, 2, 3, 4, 5];
        let nev = NonEmptyVec::from_vec(original.clone()).unwrap();
        assert_eq!(nev.to_vec(), original);
    }

    #[test]
    #[should_panic(expected = "NonEmptyVec::from_vec_unchecked called with empty vec")]
    fn from_vec_unchecked_panics_on_empty() {
        NonEmptyVec::<i32>::from_vec_unchecked(vec![]);
    }

    #[test]
    fn last_returns_last_element() {
        let v = NonEmptyVec::of(1, vec![2, 3]);
        assert_eq!(*v.last(), 3);

        let single = NonEmptyVec::new(42);
        assert_eq!(*single.last(), 42);
    }

    #[test]
    fn len_always_at_least_one() {
        let v = NonEmptyVec::new(1);
        assert_eq!(v.len(), 1);

        let v = NonEmptyVec::of(1, vec![2, 3, 4]);
        assert_eq!(v.len(), 4);
    }

    #[test]
    fn into_vec_preserves_order() {
        let v = NonEmptyVec::of(1, vec![2, 3]);
        assert_eq!(v.into_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn map_transforms_all_elements() {
        let v = nev![1, 2, 3];
        let mapped = v.map(|x| x * 2);
        assert_eq!(mapped.to_vec(), vec![2, 4, 6]);
    }

    #[test]
    fn map_identity() {
        let v = nev![1, 2, 3];
        let mapped = v.map(|x| *x);
        assert_eq!(mapped.to_vec(), v.to_vec());
    }

    #[test]
    fn flat_map_expands_and_flattens() {
        let v = nev![1, 2, 3];
        let result = v.flat_map(|x| nev![*x, *x * 10]);
        assert_eq!(result.to_vec(), vec![1, 10, 2, 20, 3, 30]);
    }

    #[test]
    fn push_returns_new_vec() {
        let v = nev![1, 2];
        let v2 = v.push(3);
        assert_eq!(v.len(), 2); // original unchanged
        assert_eq!(v2.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn push_mut_modifies_in_place() {
        let mut v = nev![1, 2];
        v.push_mut(3);
        assert_eq!(v.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn append_combines_two_vecs() {
        let a = nev![1, 2];
        let b = nev![3, 4];
        let combined = a.append(&b);
        assert_eq!(combined.to_vec(), vec![1, 2, 3, 4]);
    }

    #[test]
    fn fold_accumulates() {
        let v = nev![1, 2, 3, 4];
        let sum = v.fold(0, |acc, x| acc + x);
        assert_eq!(sum, 10);
    }

    #[test]
    fn reduce_uses_head_as_init() {
        let v = nev![1, 2, 3];
        let sum = v.reduce(|a, b| a + b);
        assert_eq!(sum, 6);
    }

    #[test]
    fn iter_visits_all_elements() {
        let v = nev![1, 2, 3];
        let collected: Vec<&i32> = v.iter().collect();
        assert_eq!(collected, vec![&1, &2, &3]);
    }

    #[test]
    fn into_iter_owns_elements() {
        let v = nev![1, 2, 3];
        let collected: Vec<i32> = v.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn contains_finds_elements() {
        let v = nev![1, 2, 3];
        assert!(v.contains(&1));
        assert!(v.contains(&3));
        assert!(!v.contains(&4));
    }

    #[test]
    fn find_returns_first_match() {
        let v = nev![1, 2, 3, 4];
        assert_eq!(v.find(|x| *x > 2), Some(&3));
        assert_eq!(v.find(|x| *x > 10), None);
    }

    #[test]
    fn zip_pairs_elements() {
        let a = nev![1, 2, 3];
        let b = nev!["a", "b"];
        let zipped = a.zip(&b);
        assert_eq!(zipped.to_vec(), vec![(&1, &"a"), (&2, &"b")]);
    }

    #[test]
    fn display_formats_correctly() {
        let v = nev![1, 2, 3];
        assert_eq!(format!("{}", v), "[1, 2, 3]");

        let single = nev![42];
        assert_eq!(format!("{}", single), "[42]");
    }

    #[test]
    fn debug_formats_as_list() {
        let v = nev![1, 2, 3];
        assert_eq!(format!("{:?}", v), "[1, 2, 3]");
    }

    #[test]
    fn equality_works() {
        let a = nev![1, 2, 3];
        let b = nev![1, 2, 3];
        let c = nev![1, 2, 4];
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn hash_is_consistent() {
        use std::collections::hash_map::DefaultHasher;
        let a = nev![1, 2, 3];
        let b = nev![1, 2, 3];
        let hash_a = {
            let mut h = DefaultHasher::new();
            a.hash(&mut h);
            h.finish()
        };
        let hash_b = {
            let mut h = DefaultHasher::new();
            b.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash_a, hash_b);
    }

    #[test]
    fn nev_macro_single() {
        let v = nev![42];
        assert_eq!(*v.head(), 42);
        assert_eq!(v.len(), 1);
    }

    #[test]
    fn nev_macro_multiple() {
        let v = nev![1, 2, 3];
        assert_eq!(v.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn nev_macro_trailing_comma() {
        let v = nev![1, 2, 3,];
        assert_eq!(v.to_vec(), vec![1, 2, 3]);
    }

    #[test]
    fn exact_size_iterator() {
        let v = nev![1, 2, 3];
        let iter = v.iter();
        assert_eq!(iter.len(), 3);
    }
}

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        fn arb_non_empty_vec()(head in any::<i32>(), tail in prop::collection::vec(any::<i32>(), 0..20)) -> NonEmptyVec<i32> {
            NonEmptyVec::of(head, tail)
        }
    }

    proptest! {
        #[test]
        fn len_always_positive(v in arb_non_empty_vec()) {
            prop_assert!(v.len() >= 1);
        }

        #[test]
        fn len_equals_head_plus_tail(v in arb_non_empty_vec()) {
            prop_assert_eq!(v.len(), 1 + v.tail().len());
        }

        #[test]
        fn to_vec_roundtrip(v in arb_non_empty_vec()) {
            let vec = v.to_vec();
            let recovered = NonEmptyVec::from_vec(vec).unwrap();
            prop_assert_eq!(v, recovered);
        }

        #[test]
        fn map_preserves_length(v in arb_non_empty_vec()) {
            let mapped = v.map(|x| x.wrapping_add(1));
            prop_assert_eq!(v.len(), mapped.len());
        }

        #[test]
        fn map_identity_law(v in arb_non_empty_vec()) {
            let mapped = v.map(|x| *x);
            prop_assert_eq!(v.to_vec(), mapped.to_vec());
        }

        #[test]
        fn from_vec_none_for_empty(_x in 0..1i32) {
            let v: Vec<i32> = vec![];
            prop_assert!(NonEmptyVec::from_vec(v).is_none());
        }

        #[test]
        fn head_is_first_element(v in arb_non_empty_vec()) {
            let vec = v.to_vec();
            prop_assert_eq!(v.head(), &vec[0]);
        }

        #[test]
        fn last_is_last_element(v in arb_non_empty_vec()) {
            let vec = v.to_vec();
            prop_assert_eq!(v.last(), &vec[vec.len() - 1]);
        }
    }
}

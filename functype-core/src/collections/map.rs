use rpds::HashTrieMapSync;
use std::fmt;
use std::hash::Hash;

/// A persistent, immutable hash map backed by `rpds::HashTrieMapSync`.
///
/// Thread-safe (Send + Sync) via Arc-based structural sharing.
///
/// # Examples
/// ```
/// use functype_core::map;
/// use functype_core::collections::map::Map;
///
/// let m = map!{ "a" => 1, "b" => 2 };
/// assert_eq!(m.get(&"a"), Some(&1));
/// assert_eq!(m.len(), 2);
///
/// let m2 = m.insert("c", 3);
/// assert_eq!(m2.len(), 3);
/// assert_eq!(m.len(), 2); // original unchanged
/// ```
#[derive(Clone)]
pub struct Map<K: Eq + Hash + Clone, V: Clone>(HashTrieMapSync<K, V>);

impl<K: Eq + Hash + Clone, V: Clone> Map<K, V> {
    /// Creates an empty map.
    pub fn new() -> Self {
        Map(HashTrieMapSync::new_sync())
    }

    /// Returns a new map with the key-value pair inserted (or updated).
    pub fn insert(&self, key: K, value: V) -> Self {
        Map(self.0.insert(key, value))
    }

    /// Returns a new map with the key removed.
    pub fn remove(&self, key: &K) -> Self {
        Map(self.0.remove(key))
    }

    /// Returns a reference to the value associated with the key.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.0.get(key)
    }

    /// Returns `true` if the map contains the key.
    pub fn contains_key(&self, key: &K) -> bool {
        self.0.contains_key(key)
    }

    /// Returns the number of entries.
    pub fn len(&self) -> usize {
        self.0.size()
    }

    /// Returns `true` if the map has no entries.
    pub fn is_empty(&self) -> bool {
        self.0.size() == 0
    }

    /// Returns the value for the key, or computes a default.
    pub fn get_or_else<F: FnOnce() -> V>(&self, key: &K, default: F) -> V {
        match self.get(key) {
            Some(v) => v.clone(),
            None => default(),
        }
    }

    /// Returns an iterator over keys.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.0.keys()
    }

    /// Returns an iterator over values.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.0.values()
    }

    /// Returns an iterator over key-value pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter()
    }

    /// Returns a new map with all values transformed by the function.
    pub fn map_values<U: Clone, F: Fn(&V) -> U>(&self, f: F) -> Map<K, U> {
        let mut result = HashTrieMapSync::new_sync();
        for (k, v) in self.0.iter() {
            result = result.insert(k.clone(), f(v));
        }
        Map(result)
    }

    /// Returns a new map containing only entries that satisfy the predicate.
    pub fn filter<F: Fn(&K, &V) -> bool>(&self, f: F) -> Self {
        let mut result = HashTrieMapSync::new_sync();
        for (k, v) in self.0.iter() {
            if f(k, v) {
                result = result.insert(k.clone(), v.clone());
            }
        }
        Map(result)
    }

    /// Merges another map into this one. Values from `other` take precedence.
    pub fn merge(&self, other: &Map<K, V>) -> Self {
        let mut result = self.0.clone();
        for (k, v) in other.0.iter() {
            result = result.insert(k.clone(), v.clone());
        }
        Map(result)
    }
}

impl<K: Eq + Hash + Clone, V: Clone> Default for Map<K, V> {
    fn default() -> Self {
        Map::new()
    }
}

impl<K: Eq + Hash + Clone + PartialEq, V: Clone + PartialEq> PartialEq for Map<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        self.iter().all(|(k, v)| other.get(k) == Some(v))
    }
}

impl<K: Eq + Hash + Clone, V: Clone + Eq> Eq for Map<K, V> {}

impl<K: Eq + Hash + Clone + fmt::Debug, V: Clone + fmt::Debug> fmt::Debug for Map<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Eq + Hash + Clone, V: Clone> FromIterator<(K, V)> for Map<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut map = HashTrieMapSync::new_sync();
        for (k, v) in iter {
            map = map.insert(k, v);
        }
        Map(map)
    }
}

/// Creates a `Map` from key-value pairs.
///
/// # Examples
/// ```
/// use functype_core::map;
///
/// let m = map!{ "a" => 1, "b" => 2 };
/// assert_eq!(m.get(&"a"), Some(&1));
///
/// let empty: functype_core::collections::map::Map<String, i32> = map!{};
/// assert!(empty.is_empty());
/// ```
#[macro_export]
macro_rules! map {
    {} => {
        $crate::collections::map::Map::new()
    };
    { $($key:expr => $value:expr),+ $(,)? } => {
        {
            let mut m = $crate::collections::map::Map::new();
            $(
                m = m.insert($key, $value);
            )+
            m
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_creates_empty() {
        let m: Map<String, i32> = Map::new();
        assert!(m.is_empty());
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn insert_and_get() {
        let m = Map::new().insert("a", 1);
        assert_eq!(m.get(&"a"), Some(&1));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn insert_is_immutable() {
        let m1 = Map::new().insert("a", 1);
        let m2 = m1.insert("b", 2);
        assert_eq!(m1.len(), 1); // original unchanged
        assert_eq!(m2.len(), 2);
    }

    #[test]
    fn insert_overwrites() {
        let m = Map::new().insert("a", 1).insert("a", 2);
        assert_eq!(m.get(&"a"), Some(&2));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn remove_key() {
        let m = Map::new().insert("a", 1).insert("b", 2);
        let m2 = m.remove(&"a");
        assert_eq!(m2.len(), 1);
        assert_eq!(m2.get(&"a"), None);
        assert_eq!(m.len(), 2); // original unchanged
    }

    #[test]
    fn contains_key() {
        let m = Map::new().insert("a", 1);
        assert!(m.contains_key(&"a"));
        assert!(!m.contains_key(&"b"));
    }

    #[test]
    fn get_or_else_present() {
        let m = Map::new().insert("a", 42);
        assert_eq!(m.get_or_else(&"a", || 0), 42);
    }

    #[test]
    fn get_or_else_absent() {
        let m: Map<&str, i32> = Map::new();
        assert_eq!(m.get_or_else(&"a", || 99), 99);
    }

    #[test]
    fn map_values_transforms() {
        let m = map! { "a" => 1, "b" => 2 };
        let mapped = m.map_values(|v| v * 10);
        assert_eq!(mapped.get(&"a"), Some(&10));
        assert_eq!(mapped.get(&"b"), Some(&20));
    }

    #[test]
    fn filter_entries() {
        let m = map! { "a" => 1, "b" => 2, "c" => 3 };
        let filtered = m.filter(|_, v| *v > 1);
        assert_eq!(filtered.len(), 2);
        assert!(!filtered.contains_key(&"a"));
    }

    #[test]
    fn merge_maps() {
        let m1 = map! { "a" => 1, "b" => 2 };
        let m2 = map! { "b" => 20, "c" => 3 };
        let merged = m1.merge(&m2);
        assert_eq!(merged.get(&"a"), Some(&1));
        assert_eq!(merged.get(&"b"), Some(&20)); // m2 takes precedence
        assert_eq!(merged.get(&"c"), Some(&3));
        assert_eq!(merged.len(), 3);
    }

    #[test]
    fn equality() {
        let a = map! { "x" => 1, "y" => 2 };
        let b = map! { "y" => 2, "x" => 1 };
        let c = map! { "x" => 1, "y" => 3 };
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn from_iterator() {
        let m: Map<&str, i32> = vec![("a", 1), ("b", 2)].into_iter().collect();
        assert_eq!(m.len(), 2);
        assert_eq!(m.get(&"a"), Some(&1));
    }

    #[test]
    fn keys_and_values() {
        let m = map! { "a" => 1, "b" => 2 };
        let mut keys: Vec<&&str> = m.keys().collect();
        keys.sort();
        assert_eq!(keys, vec![&"a", &"b"]);

        let mut vals: Vec<&i32> = m.values().collect();
        vals.sort();
        assert_eq!(vals, vec![&1, &2]);
    }

    #[test]
    fn map_macro_empty() {
        let m: Map<String, i32> = map! {};
        assert!(m.is_empty());
    }

    #[test]
    fn map_macro_entries() {
        let m = map! { "a" => 1, "b" => 2, "c" => 3 };
        assert_eq!(m.len(), 3);
    }

    #[test]
    fn map_macro_trailing_comma() {
        let m = map! { "a" => 1, "b" => 2, };
        assert_eq!(m.len(), 2);
    }

    #[test]
    fn default_is_empty() {
        let m: Map<String, i32> = Map::default();
        assert!(m.is_empty());
    }

    #[test]
    fn structural_sharing() {
        let m1 = map! { "a" => 1, "b" => 2 };
        let m2 = m1.insert("c", 3);
        // Both maps share structure for "a" and "b"
        assert_eq!(m1.len(), 2);
        assert_eq!(m2.len(), 3);
    }
}

use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::vec::IntoIter;

/// A custom `VecHashMap` struct that maintains the order of keys.
/// It wraps a `Vec` to store keys and a `HashMap` to store key-value pairs.
#[derive(Clone, Debug, PartialEq)]
pub struct VecHashMap<K: Eq + Hash + Clone, V> {
  pub values: Vec<(K, V)>,
  pub map: HashMap<K, usize>,
}

impl<K: Eq + Hash + Clone, V> VecHashMap<K, V> {
  /// Creates a new empty `VecHashMap`.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let ordered_map: VecHashMap<String, i32> = VecHashMap::new();
  /// ```
  pub fn new() -> Self {
    VecHashMap {
      values: Vec::new(),
      map: HashMap::new(),
    }
  }

  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// assert!(ordered_map.contains_key(&"key1".to_string()));
  /// ```
  pub fn contains_key(&self, k: &K) -> bool {
    self.map.contains_key(k)
  }

  /// Inserts a key-value pair into the map. If the map did not have this key present, `None` is returned.
  /// If the map did have this key present, the value is updated, and the old value is returned.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 99);
  /// assert_eq!(ordered_map.get(&"key1".to_string()), Some(&99));
  /// ```
  pub fn insert(&mut self, key: K, value: V) {
    if !self.map.contains_key(&key) {
      let idx = self.values.len();
      self.values.push((key.clone(), value));
      self.map.insert(key, idx);
      return;
    }

    let idx = self.map.get(&key).unwrap();
    self.values[*idx] = (key, value);
  }

  /// Removes a key from the map, returning the value at the key if the key was previously in the map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// assert_eq!(ordered_map.remove(&"key1".to_string()), Some(42));
  /// ```
  pub fn remove(&mut self, key: &K) -> Option<V> {
    if let Some(idx) = self.map.remove(&key) {
      let (_, v) = self.values.remove(idx);
      // Shifting Indices to left
      for (_, cidx) in self.map.iter_mut() {
        if *cidx > idx {
          *cidx -= 1
        }
      }
      return Some(v);
    }
    None
  }

  /// Gets the value of the specified key.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// assert_eq!(ordered_map.get(&"key1".to_string()), Some(&42));
  /// ```
  pub fn get(&self, key: &K) -> Option<&V> {
    if let Some(idx) = self.map.get(key) {
      return Some(&self.values[*idx].1);
    }

    None
  }

  /// Gets a mutable reference to the value of the specified key.
  //////

  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// *ordered_map.get_mut(&"key1".to_string()).unwrap() += 1;
  /// assert_eq!(ordered_map.get(&"key1".to_string()), Some(&43));
  /// ```
  pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
    if let Some(idx) = self.map.get(key) {
      if let Some(val) = self.values.get_mut(*idx) {
        return Some(&mut val.1);
      }
      return None;
    }

    None
  }

  /// Returns an iterator over the values in the ordered hash map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// ordered_map.insert("key2".to_string(), 24);
  /// let values: Vec<_> = ordered_map.values().collect();
  /// assert_eq!(values, vec![&42, &24]);
  /// ```
  pub fn values(&self) -> impl Iterator<Item=&V> {
    return VecHashMapValuesIter {
      index: 0,
      vec: &self.values,
    };
  }

  /// Returns a mutable iterator over the values in the ordered hash map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// ordered_map.insert("key2".to_string(), 24);
  /// ordered_map.values_mut().for_each(|value| *value += 1);
  /// assert_eq!(ordered_map.get(&"key1".to_string()), Some(&43));
  /// assert_eq!(ordered_map.get(&"key2".to_string()), Some(&25));
  /// ```
  pub fn values_mut(&mut self) -> impl Iterator<Item=&mut V> {
    return VecHashMapValuesMutIter {
      index: 0,
      vec: &mut self.values as *mut Vec<(K, V)>,
      _marker: PhantomData,
    };
  }

  /// Returns an iterator over the keys in the ordered hash map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// ordered_map.insert("key2".to_string(), 24);
  /// let keys: Vec<_> = ordered_map.keys().collect();
  /// assert_eq!(keys, vec![&"key1".to_string(), &"key2".to_string()]);
  /// ```
  pub fn keys(&self) -> impl Iterator<Item=&K> {
    return VecHashMapKeysIter {
      index: 0,
      vec: &self.values,
    };
  }

  /// Returns an iterator over the key-value pairs in the ordered hash map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// ordered_map.insert("key2".to_string(), 24);
  /// let pairs: Vec<_> = ordered_map.iter().collect();
  /// assert_eq!(pairs, vec![&("key1".to_string(), 42), &("key2".to_string(), 24)]);
  /// ```
  pub fn iter(&self) -> impl Iterator<Item=&(K, V)> {
    self.values.iter()
  }

  /// Returns an into iterator of the key-value pairs in the map, in the order corresponding to their keys.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// ordered_map.insert("key2".to_string(), 24);
  /// let pairs: Vec<_> = ordered_map.iter().collect();
  /// assert_eq!(pairs, vec![&("key1".to_string(), 42), &("key2".to_string(), 24)]);
  /// ```
  pub fn into_iter(self) -> IntoIter<(K, V)> {
    self.values.into_iter()
  }


  /// Returns a mutable iterator over the key-value pairs in the ordered hash map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  /// let mut ordered_map = VecHashMap::new();
  /// ordered_map.insert("key1".to_string(), 42);
  /// ordered_map.insert("key2".to_string(), 24);
  /// ordered_map.iter_mut().for_each(|(key, value)| *value += 1);
  /// assert_eq!(ordered_map.get(&"key1".to_string()), Some(&43));
  /// assert_eq!(ordered_map.get(&"key2".to_string()), Some(&25));
  /// ```
  pub fn iter_mut(&mut self) -> impl Iterator<Item=&mut (K, V)> {
    self.values.iter_mut()
  }


  /// Returns a vector of the values in the map, in the order corresponding to their keys.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  ///
  /// let mut map = VecHashMap::new();
  /// map.insert(1, "one");
  /// map.insert(2, "two");
  /// map.insert(3, "three");
  ///
  /// let values: Vec<_> = map.into_values().collect();
  /// assert_eq!(values, vec!["one", "two", "three"]);
  /// ```
  pub fn into_values(self) -> VecHashMapIntoValuesIter<K, V> {
    VecHashMapIntoValuesIter {
      vec: self.values.into_iter()
    }
  }


  /// Adds all key-value pairs from another `VecHashMap` to this one, without replacing any existing pairs.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  ///
  /// let mut map1 = VecHashMap::new();
  /// map1.insert(1, "one");
  ///
  /// let mut map2 = VecHashMap::new();
  /// map2.insert(2, "two");
  ///
  /// map1.extend(map2);
  ///
  /// assert_eq!(map1.get(&1), Some(&"one"));
  /// assert_eq!(map1.get(&2), Some(&"two"));
  /// ```
  pub fn extend(&mut self, slice: VecHashMap<K, V>) {
    slice.values.into_iter().for_each(|k| {
      if !self.map.contains_key(&k.0) {
        let idx = self.values.len();
        self.map.insert(k.0.clone(), idx.clone());
        self.values.push(k);
      } else {
        let idx = self.map[&k.0];
        self.values[idx] = k;
      }
    });
  }

  /// Returns the number of key-value pairs in the map.
  ///
  /// # Examples
  ///
  /// ```
  /// use ordered_hashmap::VecHashMap;
  ///
  /// let mut map = VecHashMap::new();
  /// assert_eq!(map.len(), 0);
  ///
  /// map.insert(1, "one");
  /// assert_eq!(map.len(), 1);
  ///
  /// map.insert(2, "two");
  /// assert_eq!(map.len(), 2);
  /// ```
  pub fn len(&self) -> usize {
    self.values.len()
  }
}

pub struct VecHashMapIntoValuesIter<K: Eq + Hash + Clone, V> {
  vec: IntoIter<(K, V)>,
}

impl<K: Eq + Hash + Clone, V> Iterator for VecHashMapIntoValuesIter<K, V> {
  type Item = V;

  fn next(&mut self) -> Option<Self::Item> {
    if let Some(val) = self.vec.next() {
      return Some(val.1);
    }

    None
  }
}

pub struct VecHashMapKeysIter<'a, K: Eq + Hash + Clone, V> {
  index: usize,
  vec: &'a Vec<(K, V)>,
}

impl<'a, K: Eq + Hash + Clone, V> Iterator for VecHashMapKeysIter<'a, K, V> {
  type Item = &'a K;

  fn next(&mut self) -> Option<Self::Item> {
    if self.index < self.vec.len() {
      let item = Some(&self.vec[self.index].0);
      self.index += 1;
      return item;
    }

    None
  }
}

pub struct VecHashMapValuesIter<'a, K: Eq + Hash + Clone, V> {
  index: usize,
  vec: &'a Vec<(K, V)>,
}

impl<'a, K: Eq + Hash + Clone, V> Iterator for VecHashMapValuesIter<'a, K, V> {
  type Item = &'a V;

  fn next(&mut self) -> Option<Self::Item> {
    if self.index < self.vec.len() {
      let item = Some(&self.vec[self.index].1);
      self.index += 1;
      return item;
    }

    None
  }
}

pub struct VecHashMapValuesMutIter<'a, K: Eq + Hash + Clone, V> {
  index: usize,
  vec: *mut Vec<(K, V)>,
  _marker: PhantomData<&'a mut Vec<(K, V)>>,
}

impl<'a, K: Eq + Hash + Clone, V: 'a> Iterator for VecHashMapValuesMutIter<'a, K, V> {
  type Item = &'a mut V;

  fn next(&mut self) -> Option<Self::Item> {
    unsafe {
      if self.index < (*self.vec).len() {
        if let Some(val) = (*self.vec).get_mut(self.index) {
          let item = Some(&mut val.1);
          self.index += 1;
          return item;
        }
      }
    }

    None
  }
}
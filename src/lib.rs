use std::collections::HashMap;
use std::hash::Hash;
use std::collections::hash_map::Entry as StdEntry;

#[derive(Clone, Debug)]
pub struct LinkedHashMap<K, V> {
  keys: Vec<K>,
  map: HashMap<K, V>,
}

impl<K: Eq + Hash + Clone, V> LinkedHashMap<K, V> {
  pub fn new() -> Self {
    LinkedHashMap {
      keys: Vec::new(),
      map: HashMap::new(),
    }
  }

  pub fn contains_key(&self, k: &K) -> bool {
    self.map.contains_key(k)
  }

  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    if !self.map.contains_key(&key) {
      self.keys.push(key.clone());
    }
    self.map.insert(key, value)
  }

  pub fn remove(&mut self, key: &K) -> Option<V> {
    self.keys.retain(|k| k != key);
    self.map.remove(key)
  }

  pub fn get(&self, key: &K) -> Option<&V> {
    self.map.get(key)
  }

  pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
    self.map.get_mut(key)
  }

  pub fn values(&self) -> impl Iterator<Item = &V> {
    self.keys.iter().filter_map(|k| self.map.get(k))
  }

  pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
    let map_ptr = &mut self.map as *mut HashMap<K, V>;
    self.keys.iter().filter_map(move |k| unsafe { (*map_ptr).get_mut(k) })
  }

  pub fn keys(&self) -> impl Iterator<Item = &K> {
    self.keys.iter()
  }

  pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
    self.keys.iter().filter_map(move |k| self.map.get(k).map(|v| (k, v)))
  }

  pub fn entry(&mut self, key: K) -> Entry<K, V> {
    match self.map.entry(key.clone()) {
      StdEntry::Occupied(occupied) => Entry::Occupied(occupied),
      StdEntry::Vacant(vacant) => {
        self.keys.push(key.clone());
        Entry::Vacant(vacant)
      }
    }
  }

  pub fn iter_mut(&mut self) -> impl Iterator<Item = (&K, &mut V)> {
    let map_ptr = &mut self.map as *mut HashMap<K, V>;
    self.keys.iter().filter_map(move |k| unsafe { (*map_ptr).get_mut(k).map(|v| (k, v)) })
  }
}

pub enum Entry<'a, K: 'a, V: 'a> {
  Occupied(std::collections::hash_map::OccupiedEntry<'a, K, V>),
  Vacant(std::collections::hash_map::VacantEntry<'a, K, V>),
}

impl<'a, K: Eq + Hash, V> Entry<'a, K, V> {
  pub fn or_insert(self, default: V) -> &'a mut V {
    match self {
      Entry::Occupied(occupied) => occupied.into_mut(),
      Entry::Vacant(vacant) => vacant.insert(default),
    }
  }

  pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
    match self {
      Entry::Occupied(occupied) => occupied.into_mut(),
      Entry::Vacant(vacant) => vacant.insert(default()),
    }
  }
}

impl<K: Eq + Hash + Clone, V> IntoIterator for LinkedHashMap<K, V> {
  type Item = (K, V);
  type IntoIter = std::vec::IntoIter<Self::Item>;

  fn into_iter(self) -> Self::IntoIter {
    let mut extracted_items: Vec<(K, V)> = self.map.into_iter().collect();
    self.keys.into_iter()
      .filter_map(move |k| {
        if let Some(index) = extracted_items.iter().position(|(key, _)| *key == k) {
          Some(extracted_items.remove(index))
        } else {
          None
        }
      })
      .collect::<Vec<_>>()
      .into_iter()
  }
}
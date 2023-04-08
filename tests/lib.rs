#[cfg(test)]
mod tests {
  use ordered_hashmap::{Entry, OrderedHashMap};

  #[test]
  fn test_new() {
    let ordered_map: OrderedHashMap<String, i32> = OrderedHashMap::new();
    assert!(ordered_map.keys.is_empty());
    assert!(ordered_map.map.is_empty());
  }

  #[test]
  fn test_insert() {
    let mut ordered_map = OrderedHashMap::new();
    assert_eq!(ordered_map.insert("key1".to_string(), 42), None);
    assert_eq!(ordered_map.get(&"key1".to_string()), Some(&42));
    assert_eq!(ordered_map.insert("key1".to_string(), 99), Some(42));
    assert_eq!(ordered_map.get(&"key1".to_string()), Some(&99));
  }

  #[test]
  fn test_remove() {
    let mut ordered_map = OrderedHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    assert_eq!(ordered_map.remove(&"key1".to_string()), Some(42));
    assert_eq!(ordered_map.remove(&"key1".to_string()), None);
  }

  #[test]
  fn test_contains_key() {
    let mut ordered_map = OrderedHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    assert!(ordered_map.contains_key(&"key1".to_string()));
    assert!(!ordered_map.contains_key(&"key2".to_string()));
  }

  #[test]
  fn test_iter() {
    let mut ordered_map = OrderedHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    ordered_map.insert("key2".to_string(), 24);
    let mut iterator = ordered_map.iter();

    assert_eq!(iterator.next(), Some((&"key1".to_string(), &42)));
    assert_eq!(iterator.next(), Some((&"key2".to_string(), &24)));
    assert_eq!(iterator.next(), None);
  }

  #[test]
  fn test_entry() {
    let mut ordered_map = OrderedHashMap::new();
    ordered_map.insert("key1".to_string(), 42);

    if let Entry::Occupied(mut entry) = ordered_map.entry("key1".to_string()) {
      *entry.get_mut() = 99;
    }

    assert_eq!(ordered_map.get(&"key1".to_string()), Some(&99));

    if let Entry::Vacant(entry) = ordered_map.entry("key2".to_string()) {
      entry.insert(24);
    }

    assert_eq!(ordered_map.get(&"key2".to_string()), Some(&24));
  }

  #[test]
  fn test_into_iter() {
    let mut ordered_map = OrderedHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    ordered_map.insert("key2".to_string(), 24);

    let mut iterator = ordered_map.into_iter();

    assert_eq!(iterator.next(), Some(("key1".to_string(), 42)));
    assert_eq!(iterator.next(), Some(("key2".to_string(), 24)));
    assert_eq!(iterator.next(), None);
  }
}
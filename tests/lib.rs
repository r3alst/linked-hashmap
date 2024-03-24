#[cfg(test)]
mod tests {
  use ordered_hashmap::{VecHashMap};

  #[test]
  fn test_new() {
    let ordered_map: VecHashMap<String, i32> = VecHashMap::new();
    assert!(ordered_map.values.is_empty());
    assert!(ordered_map.map.is_empty());
  }

  #[test]
  fn test_insert() {
    let mut ordered_map = VecHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    assert_eq!(ordered_map.get(&"key1".to_string()), Some(&42));
    ordered_map.insert("key1".to_string(), 99);
    assert_eq!(ordered_map.get(&"key1".to_string()), Some(&99));
  }

  #[test]
  fn test_remove() {
    let mut ordered_map = VecHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    assert_eq!(ordered_map.remove(&"key1".to_string()), Some(42));
    assert_eq!(ordered_map.remove(&"key1".to_string()), None);
  }

  #[test]
  fn test_contains_key() {
    let mut ordered_map = VecHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    assert!(ordered_map.contains_key(&"key1".to_string()));
    assert!(!ordered_map.contains_key(&"key2".to_string()));
  }

  #[test]
  fn test_iter() {
    let mut ordered_map = VecHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    ordered_map.insert("key2".to_string(), 24);
    let mut iterator = ordered_map.iter();

    assert_eq!(iterator.next(), Some(&("key1".to_string(), 42)));
    assert_eq!(iterator.next(), Some(&("key2".to_string(), 24)));
    assert_eq!(iterator.next(), None);
  }

  #[test]
  fn test_into_iter() {
    let mut ordered_map = VecHashMap::new();
    ordered_map.insert("key1".to_string(), 42);
    ordered_map.insert("key2".to_string(), 24);

    let mut iterator = ordered_map.into_iter();

    assert_eq!(iterator.next(), Some(("key1".to_string(), 42)));
    assert_eq!(iterator.next(), Some(("key2".to_string(), 24)));
    assert_eq!(iterator.next(), None);
  }

  #[test]
  fn test_extend() {
    let mut map1 = VecHashMap::new();
    map1.insert(1, "one");
    map1.insert(2, "two");

    let mut map2 = VecHashMap::new();
    map2.insert(2, "TWO");
    map2.insert(3, "three");

    map1.extend(map2);

    assert_eq!(map1.len(), 3);
    assert_eq!(map1.get(&1), Some(&"one"));
    assert_eq!(map1.get(&2), Some(&"TWO"));
    assert_eq!(map1.get(&3), Some(&"three"));
  }

  #[test]
  fn test_len() {
    let mut map = VecHashMap::new();

    assert_eq!(map.len(), 0);

    map.insert(1, "one");
    assert_eq!(map.len(), 1);

    map.insert(2, "two");
    assert_eq!(map.len(), 2);

    map.insert(3, "three");
    assert_eq!(map.len(), 3);
  }
}
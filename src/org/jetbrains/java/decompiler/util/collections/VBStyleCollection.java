// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.util.collections;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Objects;

public class VBStyleCollection<E, K> extends ArrayList<E> {

  private HashMap<K, Integer> map = new HashMap<>();

  private ArrayList<K> lstKeys = new ArrayList<>();

  /**
   * The most recent {@link #getWithKey} answer. Consecutive lookups of the same key (the common
   * case while printing one method) then skip the map. The entry is immutable and replaced as a
   * whole behind a volatile reference, so a reader racing another thread's update still sees a
   * consistent key/index pair; every structural change invalidates it.
   */
  private volatile Hit<K> lastHit;

  private record Hit<T>(T key, int index) {}

  public VBStyleCollection() {
    super();
  }

  public VBStyleCollection(int initialCapacity) {
    super(initialCapacity);
    lstKeys = new ArrayList<>(initialCapacity);
    map = new HashMap<>(initialCapacity);
  }

  @Override
  public boolean add(E element) {
    lastHit = null;
    lstKeys.add(null);
    super.add(element);
    return true;
  }

  @Override
  public boolean remove(Object element) {   // TODO: error on void remove(E element)
    throw new RuntimeException("not implemented!");
  }

  @Override
  public boolean addAll(Collection<? extends E> c) {
    lastHit = null;
    for (int i = c.size() - 1; i >= 0; i--) {
      lstKeys.add(null);
    }
    return super.addAll(c);
  }

  public void addAllWithKey(Collection<E> elements, Collection<K> keys) {
    lastHit = null;
    int index = super.size();

    for (K key : keys) {
      map.put(key, index++);
    }

    super.addAll(elements);
    lstKeys.addAll(keys);
  }

  public void addWithKey(E element, K key) {
    lastHit = null;
    map.put(key, super.size());
    super.add(element);
    lstKeys.add(key);
  }

  // TODO: speed up the method
  public E putWithKey(E element, K key) {
    Integer index = map.get(key);
    if (index == null) {
      addWithKey(element, key);
    }
    else {
      return super.set(index, element);
    }
    return null;
  }

  @Override
  public void add(int index, E element) {
    lastHit = null;
    addToListIndex(index, 1);
    lstKeys.add(index, null);
    super.add(index, element);
  }

  public void addWithKeyAndIndex(int index, E element, K key) {
    lastHit = null;
    addToListIndex(index, 1);
    map.put(key, index);
    super.add(index, element);
    lstKeys.add(index, key);
  }

  public void removeWithKey(K key) {
    lastHit = null;
    Integer indexBox = map.get(key);
    if (indexBox == null) {
      return;
    }
    int index = indexBox;
    addToListIndex(index + 1, -1);
    super.remove(index);
    lstKeys.remove(index);
    map.remove(key);
  }

  @Override
  public E remove(int index) {
    lastHit = null;
    addToListIndex(index + 1, -1);
    K obj = lstKeys.get(index);
    if (obj != null) {
      map.remove(obj);
    }
    lstKeys.remove(index);
    return super.remove(index);
  }

  public E getWithKey(K key) {
    Hit<K> hit = lastHit;
    if (hit != null && Objects.equals(hit.key(), key)) {
      return hit.index() < 0 ? null : super.get(hit.index());
    }
    Integer index = map.get(key);
    int resolved = index == null ? -1 : index;
    lastHit = new Hit<>(key, resolved);
    return resolved < 0 ? null : super.get(resolved);
  }

  public int getIndexByKey(K key) {
    return map.get(key);
  }

  public E getLast() {
    return super.get(super.size() - 1);
  }

  public boolean containsKey(K key) {
    return map.containsKey(key);
  }

  @Override
  public void clear() {
    lastHit = null;
    map.clear();
    lstKeys.clear();
    super.clear();
  }

  @Override
  public VBStyleCollection<E, K> clone() {
    VBStyleCollection<E, K> c = new VBStyleCollection<>();
    c.addAll(new ArrayList<>(this));
    c.setMap(new HashMap<>(map));
    c.setLstKeys(new ArrayList<>(lstKeys));
    return c;
  }

  private void setMap(HashMap<K, Integer> map) {
    lastHit = null;
    this.map = map;
  }

  public K getKey(int index) {
    return lstKeys.get(index);
  }

  public ArrayList<K> getLstKeys() {
    return lstKeys;
  }

  private void setLstKeys(ArrayList<K> lstKeys) {
    lastHit = null;
    this.lstKeys = lstKeys;
  }

  private void addToListIndex(int index, int diff) {
    for (int i = lstKeys.size() - 1; i >= index; i--) {
      K obj = lstKeys.get(i);
      if (obj != null) {
        map.put(obj, i + diff);
      }
    }
  }

  public String toStringVb() {
    StringBuilder sb = new StringBuilder();
    sb.append("[");
    for (int i = 0; i < super.size(); i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(this.getLstKeys().get(i))
        .append("=")
        .append(super.get(i));
    }
    sb.append("]");
    return sb.toString();
  }
}
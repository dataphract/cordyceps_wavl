extern crate alloc;

use alloc::boxed::Box;
use core::{borrow::Borrow, marker::PhantomPinned, ptr::NonNull};

use cordyceps::Linked;

use crate::{Links, TreeNode, WavlTree};

/// An ordered map based on a [WAVL tree].
///
/// [WAVL tree]: https://en.wikipedia.org/wiki/WAVL_tree
pub struct WavlMap<K: Ord, V> {
    tree: WavlTree<MapNode<K, V>>,
}

struct MapNode<K, V> {
    links: Links<MapNode<K, V>>,
    key: K,
    value: V,
    _unpin: PhantomPinned,
}

unsafe impl<K, V> Linked<Links<MapNode<K, V>>> for MapNode<K, V> {
    type Handle = Box<Self>;

    fn into_ptr(r: Self::Handle) -> NonNull<Self> {
        Box::leak(r).into()
    }

    unsafe fn from_ptr(ptr: NonNull<Self>) -> Self::Handle {
        unsafe { Box::from_raw(ptr.as_ptr()) }
    }

    unsafe fn links(ptr: NonNull<Self>) -> NonNull<Links<MapNode<K, V>>> {
        let ptr = ptr.as_ptr();
        NonNull::new(core::ptr::addr_of_mut!((*ptr).links)).unwrap()
    }
}

impl<K: Ord, V> TreeNode<Links<MapNode<K, V>>> for MapNode<K, V> {
    type Key = K;

    fn key(&self) -> &Self::Key {
        &self.key
    }
}

impl<K: Ord, V> WavlMap<K, V> {
    /// Creates a new, empty `WavlMap`.
    pub const fn new() -> Self {
        Self {
            tree: WavlTree::new(),
        }
    }

    /// Returns `true` if the map contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// Returns the number of elements in the map.
    pub const fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns `true` if the map contains a value associated with `key`.
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.tree.contains_key(key)
    }

    /// Returns a reference to the value associated with `key`.
    #[inline]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.tree.get(key).map(|node| &node.value)
    }

    /// Returns a mutable reference to the value associated with `key`.
    #[inline]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.tree
            .get_mut(key)
            // SAFETY: Pinning is not structural for `node.value`.
            .map(|node| unsafe { &mut node.get_unchecked_mut().value })
    }

    /// Returns the first key-value pair in the map.
    ///
    /// The returned key is the minimum key in the map.
    #[inline]
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.tree.first().map(|node| (&node.key, &node.value))
    }

    /// Removes and returns the first key-value pair in the map.
    ///
    /// The returned key is the minimum key in the map.
    #[inline]
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        self.tree.pop_first().map(|node| {
            let MapNode { key, value, .. } = *node;
            (key, value)
        })
    }

    /// Returns the last key-value pair in the map.
    ///
    /// The returned key is the maximum key in the map.
    #[inline]
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.tree.last().map(|node| (&node.key, &node.value))
    }

    /// Removes and returns the last key-value pair in the map.
    ///
    /// The returned key is the maximum key in the map.
    #[inline]
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        self.tree.pop_last().map(|node| {
            let MapNode { key, value, .. } = *node;
            (key, value)
        })
    }

    /// Removes the value associated with `key` from the map.
    #[inline]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.tree.remove(key).map(|node| node.value)
    }

    /// Clears the map, removing all elements.
    #[inline]
    pub fn clear(&mut self) {
        self.tree.clear();
    }
}

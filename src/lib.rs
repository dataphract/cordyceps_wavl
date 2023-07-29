//! An intrusive weak AVL tree, or WAVL tree.
//!
//! A WAVL tree is a self-balancing binary search tree which allows insertion and lookup in
//! O(log<sub>2</sub>N) time. Deletion of a known node is O(1), requiring two tree rotations in the
//! worst case.
//!
//! WAVL trees are described in the paper [Rank-Balanced Trees] by Haeupler, Sen and Tarjan.
//!
//! [Rank-Balanced Trees]: http://arks.princeton.edu/ark:/88435/pr1nz5z

#![no_std]
#![allow(unstable_name_collisions)]

// Conventions used in comments are from Hauepler, Sen and Tarjan:
// - The rank of a node `x` is denoted `r(x)`.
// - The parent of a node `x` is denoted `p(x)`.
// - The rank difference of a node `x` is given by `r(p(x)) - r(x)`.
// - A node `x` is an `i`-child if its rank difference is `i`.
// - A node is `i,j` if one of its children is an `i`-child and the other is a `j`-child.
//
// The fundamental invariants of a WAVL tree are:
// 1. All rank differences are either 1 or 2.
// 2. All leaves have rank 0.
//
// `None` nodes are assigned a rank of -1.
use core::{
    borrow::Borrow, cell::UnsafeCell, cmp::Ordering, marker::PhantomPinned, mem, ops::Not,
    pin::Pin, ptr::NonNull,
};

use cordyceps::Linked;

use crate::rank::RankPtr;

pub use crate::iter::{Iter, IterMut};

#[cfg(feature = "alloc")]
pub use crate::map::WavlMap;

mod entry;
mod iter;
mod rank;

#[cfg(feature = "alloc")]
pub mod map;

#[cfg(any(feature = "std", test))]
pub mod debug;

#[cfg(any(feature = "model", test))]
pub mod model;

#[cfg(test)]
mod tests;

pub trait TreeNode<L>: Linked<L> {
    type Key: Ord;

    fn key(&self) -> &Self::Key;
}

/// An intrusive weak AVL tree, or WAVL tree.
///
/// [WAVL tree]: https://en.wikipedia.org/wiki/WAVL_tree
pub struct WavlTree<T>
where
    T: TreeNode<Links<T>>,
{
    root: Link<T>,
    len: usize,
}

/// Links to other nodes in a [`WavlTree`].
///
/// In order to be part of a [`WavlTree`], a type must contain a value of this type, and must
/// implement the [`TreeNode`] trait for [`Links<Self>`].
#[derive(Debug)]
pub struct Links<T> {
    inner: UnsafeCell<LinksInner<T>>,
}

unsafe impl<T: Send> Send for Links<T> {}
unsafe impl<T: Sync> Sync for Links<T> {}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Dir {
    Left = 0,
    Right = 1,
}

impl Not for Dir {
    type Output = Dir;

    fn not(self) -> Self::Output {
        match self {
            Dir::Left => Dir::Right,
            Dir::Right => Dir::Left,
        }
    }
}

#[repr(C)]
struct LinksInner<T> {
    parent_and_rank: RankPtr<T>,
    children: [Link<T>; 2],
    _unpin: PhantomPinned,
}

type Link<T> = Option<NonNull<T>>;

impl<T> WavlTree<T>
where
    T: TreeNode<Links<T>>,
{
    /// Returns a new empty tree.
    pub const fn new() -> WavlTree<T> {
        WavlTree { root: None, len: 0 }
    }

    /// Returns `true` if the tree contains no elements.
    pub const fn is_empty(&self) -> bool {
        let empty = self.len() == 0;

        if cfg!(debug_assertions) {
            // Can't use assert_eq!() in const fn.
            assert!(empty == self.root.is_none());
        }

        empty
    }

    /// Returns the number of elements in the tree.
    pub const fn len(&self) -> usize {
        self.len
    }

    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        if let Some(root) = self.root {
            unsafe { self.assert_invariants_at(root) };
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    unsafe fn assert_invariants_at(&self, node: NonNull<T>) {
        unsafe {
            let parity = self.links(node).parity();

            // Ensure all leaves have rank 0.
            if self.is_leaf(node) {
                assert!(!parity);
                return;
            }

            for child in [Dir::Left, Dir::Right] {
                if let Some(child) = self.links(node).child(child) {
                    // Ensure child's parent link points to this node.
                    let parent = self
                        .links(child)
                        .parent()
                        .expect("{child:?} child parent pointer not set");
                    assert_eq!(node, parent);

                    self.assert_invariants_at(child);
                }
            }
        }
    }

    /// Returns `true` if the tree contains an item with the specified key.
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.get(key).is_some()
    }

    /// Returns a reference to the node corresponding to `key`.
    pub fn get<Q>(&self, key: &Q) -> Option<&T>
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord,
    {
        let ptr = self.get_raw(key)?;
        unsafe { Some(ptr.as_ref()) }
    }

    /// Returns a pinned mutable reference to the node corresponding to `key`.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<Pin<&mut T>>
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord,
    {
        let mut ptr = self.get_raw(key)?;
        unsafe { Some(Pin::new_unchecked(ptr.as_mut())) }
    }

    fn get_raw<Q>(&self, key: &Q) -> Link<T>
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord,
    {
        let mut opt_cur = self.root;

        loop {
            let cur = opt_cur?;

            unsafe {
                match key.cmp(cur.as_ref().key().borrow()) {
                    Ordering::Less => opt_cur = self.links(cur).left(),
                    Ordering::Equal => return Some(cur),
                    Ordering::Greater => opt_cur = self.links(cur).right(),
                }
            }
        }
    }

    // TODO: The entry API is difficult for an intrusive map as the key and value are packaged
    // together, so the standard library approach of `tree.entry(key).insert(value)` doesn't work.
    // An easy possibility is to look up the entry with a key and then write an entire node, but
    // this either allows writing the wrong key in the node (unsafe) or requires the entry to hold a
    // reference to the key used to look up the entry, thus requiring two copies of the key.
    //
    // Another possibility is to look up the entry using a node with an initialized key but an
    // uninitialized value, and then write the value when `.insert()` is called. This avoids
    // duplicating the key and prevents the insertion of the wrong key, but will require users to
    // have a `MaybeUninit<V>` field in the node type, which in turn likely needs to be
    // trait-accessible.
    //
    // pub fn entry<'key, Q>(&mut self, key: &'key Q) -> Entry<'_, 'key, T, Q>
    // where
    //     T::Key: Borrow<Q> + Ord,
    //     Q: Ord ,
    // {
    //     let Some(mut cur) = self.root else {
    //         return unsafe { Entry::vacant_root(self, key) };
    //     };
    //
    //     loop {
    //         unsafe {
    //             match key.cmp(cur.as_ref().key().borrow()) {
    //                 Ordering::Less => match self.links(cur).left() {
    //                     Some(item) => cur = item,
    //                     None => return Entry::vacant_child(self, key, cur, Dir::Left),
    //                 },
    //
    //                 Ordering::Greater => match self.links(cur).right() {
    //                     Some(item) => cur = item,
    //                     None => return Entry::vacant_child(self, key, cur, Dir::Right),
    //                 },
    //
    //                 Ordering::Equal => return Entry::occupied(self, cur),
    //             }
    //         }
    //     }
    // }

    /// Returns the minimum element of the tree.
    pub fn first(&self) -> Option<&T> {
        self.first_raw().map(|first| unsafe { first.as_ref() })
    }

    fn first_raw(&self) -> Option<NonNull<T>> {
        let mut cur = self.root?;

        unsafe {
            while let Some(left) = self.links(cur).left() {
                cur = left;
            }

            Some(cur)
        }
    }

    /// Removes and returns the minimum element of the tree.
    pub fn pop_first(&mut self) -> Option<T::Handle> {
        let first = self.first_raw()?;

        unsafe { Some(self.remove_at(first)) }
    }

    /// Returns the maximum element of the tree.
    pub fn last(&self) -> Option<&T> {
        self.last_raw().map(|last| unsafe { last.as_ref() })
    }

    fn last_raw(&self) -> Option<NonNull<T>> {
        let mut cur = self.root?;

        unsafe {
            while let Some(right) = self.links(cur).right() {
                cur = right;
            }

            Some(cur)
        }
    }

    /// Removes and returns the maximum element of the tree.
    pub fn pop_last(&mut self) -> Option<T::Handle> {
        let last = self.last_raw()?;

        unsafe { Some(self.remove_at(last)) }
    }

    unsafe fn maybe_set_parent(&mut self, opt_node: Link<T>, parent: Link<T>) {
        let Some(node) = opt_node else {
            return;
        };

        unsafe { self.links_mut(node).set_parent(parent) };
    }

    #[inline]
    unsafe fn replace_child_or_set_root(
        &mut self,
        parent: Link<T>,
        old_child: NonNull<T>,
        new_child: Link<T>,
    ) {
        match parent {
            Some(parent) => self.replace_child(parent, old_child, new_child),
            None => self.root = new_child,
        }
    }

    // Replaces the child pointer of `parent` pointing at `old_child` with `new_child`.
    //
    // `new_child`'s parent pointer is not updated.
    //
    // # Safety
    //
    // The caller must ensure that the following conditions hold:
    // - `old_child` is a child node of `parent`.
    // - `new_child` is not a child node of `parent`.
    #[cfg(not(debug_assertions))]
    #[inline]
    unsafe fn replace_child(
        &mut self,
        parent: NonNull<T>,
        old_child: NonNull<T>,
        new_child: Option<NonNull<T>>,
    ) {
        unsafe {
            if self.links(parent).child(Dir::Left) == Some(old_child) {
                self.links_mut(parent).set_child(Dir::Left, new_child);
            } else {
                self.links_mut(parent).set_child(Dir::Right, new_child);
            }
        }
    }

    // Replaces the child pointer of `parent` pointing at `old_child` with `new_child`.
    //
    // `new_child`'s parent pointer is not updated.
    //
    // # Safety
    //
    // The caller must ensure that the following conditions hold:
    // - `old_child` is a child node of `parent`.
    // - `new_child` is not a child node of `parent`.
    #[cfg(debug_assertions)]
    unsafe fn replace_child(
        &mut self,
        parent: NonNull<T>,
        old_child: NonNull<T>,
        new_child: Option<NonNull<T>>,
    ) {
        unsafe {
            if self.links(parent).child(Dir::Left) == Some(old_child) {
                if let Some(new_child) = new_child {
                    assert_ne!(
                        self.links(parent).child(Dir::Right),
                        Some(new_child),
                        "`new_child` must not be a child of `parent`"
                    );
                }

                self.links_mut(parent).set_child(Dir::Left, new_child);
            } else if self.links(parent).child(Dir::Right) == Some(old_child) {
                if let Some(new_child) = new_child {
                    assert_ne!(
                        self.links(parent).child(Dir::Left),
                        Some(new_child),
                        "`new_child` must not be a child of `parent`"
                    );
                }

                self.links_mut(parent).set_child(Dir::Right, new_child);
            } else {
                unreachable!("`old_child` must be a child of `parent`");
            }

            if let Some(new_child) = new_child {
                self.links_mut(new_child).set_parent(Some(parent));
            }
        }
    }

    // Performs a rotation, moving `up` up and its parent `down` down.
    //
    // The ranks of affected nodes are not updated.
    fn rotate_at(&mut self, down: NonNull<T>, up: NonNull<T>) {
        unsafe {
            // - `down` becomes the `dir` child of `up`.
            // - `across` goes from the `dir` child of `up` to the `!dir` child of `down`.
            let dir = if self.links(down).right() == Some(up) {
                Dir::Left
            } else {
                Dir::Right
            };

            assert!(self.root.map(|r| r != up).unwrap_or(false));

            let across = self.links(up).child(dir);
            self.links_mut(down).set_child(!dir, across);
            self.maybe_set_parent(across, Some(down));

            self.links_mut(up).set_child(dir, Some(down));
            let parent = self.links_mut(down).set_parent(Some(up));
            self.links_mut(up).set_parent(parent);

            match parent {
                Some(parent) => self.replace_child(parent, down, Some(up)),
                None => self.root = Some(up),
            }
        }
    }

    // Performs a double rotation at the non-root node `up`.
    //
    // The ranks of affected nodes are not updated.
    fn rotate_twice_at(&mut self, down_second: NonNull<T>, down_first: NonNull<T>, up: NonNull<T>) {
        unsafe {
            let dir = if self.links(down_first).right() == Some(up) {
                Dir::Right
            } else {
                Dir::Left
            };

            let across_first = self.links(up).child(!dir);
            let across_second = self.links(up).child(dir);

            self.maybe_set_parent(across_first, Some(down_first));

            self.links_mut(down_first).set_child(dir, across_first);
            self.links_mut(down_first).set_parent(Some(up));

            self.maybe_set_parent(across_second, Some(down_second));

            T::links(down_second)
                .as_mut()
                .set_child(!dir, across_second);
            let parent = self.links_mut(down_second).set_parent(Some(up));

            self.links_mut(up).set_parent(parent);
            self.links_mut(up).set_child(!dir, Some(down_first));
            self.links_mut(up).set_child(dir, Some(down_second));

            match parent {
                Some(parent) => self.replace_child(parent, down_second, Some(up)),
                None => self.root = Some(up),
            }
        }
    }

    fn sibling(&self, parent: NonNull<T>, node: Option<NonNull<T>>) -> Link<T> {
        unsafe {
            debug_assert!(
                self.links(parent).left().is_some() || self.links(parent).right().is_some()
            );
            if self.links(parent).left() == node {
                self.links(parent).right()
            } else {
                self.links(parent).left()
            }
        }
    }

    /// Inserts an item into the tree.
    ///
    /// This operation completes in O(log<sub>2</sub>N) time, with a constant number of rotations.
    pub fn insert(&mut self, item: T::Handle) -> Option<T::Handle> {
        match self.root {
            Some(root) => unsafe { self.insert_at(root, item) },
            None => {
                unsafe { self.insert_as_root(T::into_ptr(item)) };
                None
            }
        }
    }

    unsafe fn insert_as_root(&mut self, item: NonNull<T>) {
        debug_assert!(self.root.is_none());

        unsafe {
            self.links_mut(item).set_parent(None);
            self.links_mut(item).set_left(None);
            self.links_mut(item).set_right(None);
        }

        self.root = Some(item);
        self.len += 1;
    }

    unsafe fn insert_at(&mut self, root: NonNull<T>, item: T::Handle) -> Option<T::Handle> {
        let ptr = T::into_ptr(item);

        let mut opt_cur = Some(root);

        // Descend the tree, looking for a suitable leaf.
        while let Some(cur) = opt_cur {
            let ordering = unsafe { ptr.as_ref().key().cmp(cur.as_ref().key()) };

            let dir = match ordering {
                Ordering::Less => Dir::Left,
                Ordering::Greater => Dir::Right,

                Ordering::Equal => unsafe {
                    let parent = self.links(cur).parent();
                    let left = self.links(cur).left();
                    let right = self.links(cur).right();

                    self.replace_child_or_set_root(parent, cur, Some(ptr));

                    self.maybe_set_parent(left, Some(ptr));
                    self.maybe_set_parent(right, Some(ptr));
                    let parity = self.parity(cur);

                    self.links_mut(ptr).set_parity(parity);
                    self.links_mut(ptr).set_parent(parent);
                    self.links_mut(ptr).set_left(left);
                    self.links_mut(ptr).set_right(right);

                    self.links_mut(cur).clear();
                    return Some(T::from_ptr(cur));
                },
            };

            unsafe {
                match self.links(cur).child(dir) {
                    // Descend.
                    Some(child) => opt_cur = Some(child),

                    // Set `item` as child.
                    None => {
                        self.insert_as_child(cur, dir, ptr);
                        return None;
                    }
                }
            }
        }

        unreachable!()
    }

    // Inserts `item` as a child of `parent` in direction `dir`.
    //
    // Assumes `parent` does not already have a child in that direction.
    unsafe fn insert_as_child(&mut self, parent: NonNull<T>, dir: Dir, item: NonNull<T>) {
        unsafe {
            debug_assert!(self.links(parent).child(dir).is_none());

            let parent_was_leaf = self.is_leaf(parent);
            self.links_mut(parent).set_child(dir, Some(item));
            self.links_mut(item).set_parent(Some(parent));

            if parent_was_leaf {
                // The parent node is rank 0 and the newly inserted node is also rank 0, which
                // violates the rank rule.
                self.rebalance_inserted(item);
            }

            self.len += 1;
        }
    }

    // Performs a bottom-up rebalance of the tree after the insertion of `node`.
    //
    // Invariants:
    // - Both `node` and its parent are rank 0.
    // - `node` is not the tree root.
    // - `node` has no children and is thus rank 0 and 1,1.
    // - `node`'s parent is 0,1.
    unsafe fn rebalance_inserted(&mut self, node: NonNull<T>) {
        debug_assert!(unsafe { !self.parity(node) });

        let mut x = node;
        let mut parent = unsafe {
            T::links(node)
                .as_ref()
                .parent()
                .expect("node must not be the tree root")
        };

        debug_assert!(self.sibling(parent, Some(node)).is_none());

        let mut x_parity = false;
        let mut parent_parity = false;
        let mut sibling_parity = true;

        // While `x` is not the tree root and its parent is 0,1, promote the parent and ascend.
        while x_parity == parent_parity && x_parity != sibling_parity {
            unsafe {
                // Promote the parent.
                self.promote(parent);

                // Ascend one level. If this reaches the root, break.
                (parent, x) = match self.links_mut(parent).parent() {
                    Some(p) => (p, parent),
                    None => break,
                };

                x_parity = self.parity(x);
                parent_parity = self.parity(parent);
                sibling_parity = self.opt_parity(self.sibling(parent, Some(x)));
            }
        }

        // If parent is not 0,2, the rank rule holds.
        if x_parity != parent_parity || x_parity != sibling_parity {
            return;
        }

        let z = parent;
        unsafe {
            let rotate_dir = if self.links(parent).left() == Some(x) {
                Dir::Right
            } else {
                Dir::Left
            };

            let y = self.links(x).child(rotate_dir);
            match y {
                Some(y) if x_parity != self.parity(y) => {
                    self.rotate_twice_at(z, x, y);
                    self.promote(y);
                    self.demote(x);
                }

                Some(_) | None => {
                    self.rotate_at(parent, x);
                }
            }

            // z is demoted in all cases.
            self.demote(z);
        }
    }

    // Returns the minimum node in the subtree.
    //
    // If the subtree root is not the minimum, also returns the minimum node's parent.
    #[inline]
    unsafe fn min_in_subtree(&self, root: NonNull<T>) -> (NonNull<T>, Option<NonNull<T>>) {
        let mut parent = None;
        let mut cur = root;

        while let Some(left) = unsafe { self.links(cur).left() } {
            parent = Some(cur);
            cur = left;
        }

        (cur, parent)
    }

    /// Removes the element associated with `key` from the tree.
    ///
    /// This operation completes in O(log<sub>2</sub>N) time, with a constant number of rotations.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<T::Handle>
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord,
    {
        self.get_raw(key)
            .map(|node| unsafe { self.remove_at(node) })
    }

    /// Removes an arbitrary node from the tree.
    ///
    /// This operation completes in O(log<sub>2</sub>N) time, with a constant number of rotations.
    ///
    /// # Safety
    ///
    /// It is the caller's responsibility to ensure that `node` is an element of `self`, and not any
    /// other tree.
    pub unsafe fn remove_at(&mut self, node: NonNull<T>) -> T::Handle {
        // There are three possible cases:
        //
        // 1. `node` has two children.
        //
        //    In this case `node`'s successor[^1] is removed from the tree and assumes `node`'s place
        //    and rank. The successor's right child is elevated to replace it.
        //
        //    The successor by definition has no left child, so this can be treated as a removal
        //    matching case 2 or 3.
        //
        // 2. `node` has one child.
        //
        //    In this case, the rank rule is violated if `node` is a 2-child; its sole child becomes
        //    a 3-child[^2].
        //
        // 3. `node` is a leaf.
        //
        //    In this case, the rank rule is violated if `node` is a child of a unary node (and thus
        //    a 1-child); the unary node becomes a 2,2 leaf.
        //
        // Thus, after removal and elevation, but before rebalancing, exactly one of the following
        // is true:
        //
        // 1. The rank rule holds.
        // 2. There exists exactly one leaf node which is a 3-child.
        // 3. There exists exactly one leaf node which is 2,2.
        //
        // [^1]: The successor of a node `a` is the least node in `a`'s right subtree (if `a` has a
        //       right subtree).
        // [^2]: Unary nodes have rank 1 and are 1,2 by construction; the missing child has rank -1
        //       and is a 2-child, and the present child has rank 0 and is a 1-child. Thus the
        //       elevation (not promotion) of a unary 2-child's sole child always results in a
        //       3-child.

        let removed = node;

        unsafe {
            let parent = self.links(node).parent();
            let left = self.links(node).left();
            let right = self.links(node).right();

            enum Violation<T> {
                None,
                ThreeChild(NonNull<T>, Option<NonNull<T>>),
                TwoTwoLeaf(Option<NonNull<T>>, NonNull<T>),
            }

            let violation = match (left, right) {
                (Some(left), Some(right)) => {
                    let (successor, successor_parent) = self.min_in_subtree(right);
                    let successor_right = self.links(successor).right();

                    let successor_was_2_child =
                        self.parity(successor_parent.unwrap_or(node)) == self.parity(successor);

                    if let Some(successor_parent) = successor_parent {
                        // Elevate the successor's right child to replace it.
                        self.replace_child(successor_parent, successor, successor_right);
                        self.links_mut(successor).set_right(Some(right));
                        self.links_mut(right).set_parent(Some(successor));
                    }

                    self.replace_child_or_set_root(parent, node, Some(successor));

                    // Transfer rank of `node` to `successor`.
                    let node_parity = self.links(node).parity();

                    self.links_mut(successor).set_parent(parent);
                    self.links_mut(successor).set_parity(node_parity);
                    self.links_mut(successor).set_left(Some(left));
                    // Right link is updated above iff `successor` != `right`.

                    self.links_mut(left).set_parent(Some(successor));

                    // If the successor was a 2-child, its child (which may be None) becomes a
                    // 3-child; otherwise, if the successor is not `right`, and its parent is unary,
                    // its parent becomes a 2-2 leaf; otherwise the rank rule holds.
                    successor_was_2_child
                        .then(|| {
                            let parent = successor_parent.unwrap_or(successor);
                            // If the successor was not the removed node's right child, the
                            // successor's right child becomes a 3-child of the successor's former
                            // parent. Otherwise, the subtree rooted at the successor is elevated
                            // intact.
                            Violation::ThreeChild(parent, successor_right)
                        })
                        .or_else(|| {
                            successor_parent
                                .filter(|&p| self.links(p).is_leaf())
                                .map(|sp| Violation::TwoTwoLeaf(self.links(sp).parent(), sp))
                        })
                        .unwrap_or(Violation::None)
                }

                (Some(child), None) | (None, Some(child)) => 'unary: {
                    self.replace_child_or_set_root(parent, node, Some(child));
                    self.links_mut(child).set_parent(parent);

                    // The removed node was unary. Thus the removed node was 1,2, and its child was
                    // a 1-child. If the removed node was a 2-child, its child becomes a 3-child;
                    // otherwise the rank rule holds.

                    let Some(parent) = parent else {
                        break 'unary Violation::None;
                    };

                    if self.parity(parent) == self.parity(node) {
                        Violation::ThreeChild(parent, Some(child))
                    } else {
                        Violation::None
                    }
                }

                (None, None) => 'leaf: {
                    self.replace_child_or_set_root(parent, node, None);

                    // The removed node was a leaf. If it had no parent, the tree is empty, so the
                    // rank rule holds.
                    let Some(parent) = parent else {
                        break 'leaf Violation::None;
                    };

                    let grandparent = self.links(parent).parent();

                    // If the removed node's parent was unary, the parent becomes a 2,2 leaf.
                    if self.links(parent).is_leaf() {
                        break 'leaf Violation::TwoTwoLeaf(grandparent, parent);
                    }

                    // The removed node's parent was binary. If it has rank 2, the new missing node
                    // is a 3-child.
                    if !self.parity(parent) {
                        Violation::ThreeChild(parent, None)
                    } else {
                        Violation::None
                    }
                }
            };

            match violation {
                Violation::None => (),
                Violation::ThreeChild(parent, leaf) => {
                    self.rebalance_3_child(parent, leaf);
                }
                Violation::TwoTwoLeaf(parent, leaf) => {
                    self.demote(leaf);

                    if let Some(parent) = parent {
                        if self.parity(parent) != self.parity(leaf) {
                            self.rebalance_3_child(parent, Some(leaf));
                        }
                    }
                }
            }

            self.len -= 1;

            T::from_ptr(removed)
        }
    }

    unsafe fn rebalance_3_child(&mut self, mut parent: NonNull<T>, child: Option<NonNull<T>>) {
        let mut x = child;
        let mut y = self.sibling(parent, x).unwrap();

        // On the first iteration of the loop, `x` is known to be a 3-child; on subsequent
        // iterations, `x` has just been demoted, making it either a 2-child or a 3-child of
        // `parent`. Thus a parity comparison suffices to determine whether `x` is a 3-child.
        while self.parity(parent) != self.opt_parity(x) {
            if self.parity(parent) == self.parity(y) {
                self.demote(parent);
            } else if self.is_2_2(y) {
                self.demote(y);
                self.demote(parent);
            } else {
                break;
            }

            let grandparent = match self.links(parent).parent() {
                Some(p) => p,
                None => break,
            };

            x = Some(parent);
            y = self
                .sibling(grandparent, Some(parent))
                .expect("should have a sibling");
            parent = grandparent
        }

        if self.parity(parent) == self.opt_parity(x) {
            return;
        }

        let dir = self.which_child(parent, x);

        // Here we give up on descriptive names entirely and just use the names from the paper.
        let z = parent;
        let w = self.links(y).child(!dir);

        if self.parity(y) == self.opt_parity(w) {
            let v = self.links(y).child(dir).unwrap();
            self.rotate_twice_at(z, y, v);
            self.promote_twice(v);
            self.demote(y);
            self.demote_twice(z);
        } else {
            self.rotate_at(parent, y);
            self.promote(y);

            if self.is_leaf(z) {
                self.demote_twice(z);
            } else {
                self.demote(z);
            }
        }
    }

    /// Clears the tree, removing all elements.
    pub fn clear(&mut self) {
        let mut opt_cur = self.root;

        while let Some(cur) = opt_cur {
            unsafe {
                // Descend to the minimum node.
                let (cur, parent) = self.min_in_subtree(cur);
                let parent = parent.or_else(|| self.links(cur).parent());

                let right = self.links(cur).right();

                // Elevate the node's right child (which may be None).
                self.replace_child_or_set_root(parent, cur, right);
                self.maybe_set_parent(right, parent);

                // Drop the node.
                drop(T::from_ptr(cur));
                self.len -= 1;

                // If the node had no right child, climb to the parent. If the node had no parent,
                // the tree is empty.
                opt_cur = right.or(parent);
            }
        }
    }

    /// Returns an iterator over the items in the tree, sorted by key.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    /// Returns an iterator of mutable borrows over the items in the tree, sorted by key.
    ///
    /// # Safety
    ///
    /// It is the caller's responsibility to ensure that the `Links` of returned items are not
    /// modified, as doing so can corrupt the tree, resulting in undefined behavior.
    #[must_use]
    pub unsafe fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::new(self)
    }

    // Support methods ========================================================

    #[inline]
    unsafe fn links(&self, node: NonNull<T>) -> &Links<T> {
        unsafe { T::links(node).as_ref() }
    }

    #[inline]
    unsafe fn links_mut(&mut self, node: NonNull<T>) -> &mut Links<T> {
        unsafe { T::links(node).as_mut() }
    }

    #[inline]
    unsafe fn is_leaf(&self, node: NonNull<T>) -> bool {
        unsafe {
            let inner = &*T::links(node).as_ref().inner.get();
            inner.children[0].is_none() && inner.children[1].is_none()
        }
    }

    #[inline]
    unsafe fn promote(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.parent_and_rank.promote();
        }
    }

    #[inline]
    unsafe fn promote_twice(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.parent_and_rank.promote_twice();
        }
    }

    #[inline]
    unsafe fn demote(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.parent_and_rank.demote();
        }
    }

    #[inline]
    unsafe fn demote_twice(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.parent_and_rank.demote_twice();
        }
    }

    /// Returns the rank parity of the pointed-to node.
    unsafe fn parity(&self, node: NonNull<T>) -> bool {
        T::links(node).as_ref().parity()
    }

    unsafe fn opt_parity(&self, node: Link<T>) -> bool {
        node.map(|n| self.parity(n)).unwrap_or(true)
    }

    unsafe fn is_2_2(&self, node: NonNull<T>) -> bool {
        unsafe {
            let node = T::links(node).as_ref();

            if node.parity() != self.opt_parity(node.left()) {
                return false;
            }

            node.parity() == self.opt_parity(node.right())
        }
    }

    unsafe fn which_child(&self, parent: NonNull<T>, child: Option<NonNull<T>>) -> Dir {
        if T::links(parent).as_ref().left() == child {
            Dir::Left
        } else {
            Dir::Right
        }
    }
}

impl<T> Drop for WavlTree<T>
where
    T: TreeNode<Links<T>>,
{
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T> Links<T> {
    /// Returns new links for a [`WavlTree`].
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: UnsafeCell::new(LinksInner {
                parent_and_rank: RankPtr::new(None, false),
                children: [None; 2],
                _unpin: PhantomPinned,
            }),
        }
    }

    /// Returns `true` if this node is currently linked into a [`WavlTree`].
    pub fn is_linked(&self) -> bool {
        let inner = unsafe { &*self.inner.get() };
        inner.parent_and_rank.ptr().is_some()
            || inner.children[0].is_some()
            || inner.children[1].is_some()
    }

    #[inline]
    fn is_leaf(&self) -> bool {
        self.left().is_none() && self.right().is_none()
    }

    #[inline]
    pub fn parity(&self) -> bool {
        unsafe { (*self.inner.get()).parent_and_rank.parity() }
    }

    #[inline]
    pub fn parent(&self) -> Link<T> {
        unsafe { (*self.inner.get()).parent_and_rank.ptr() }
    }

    #[inline]
    fn child(&self, dir: Dir) -> Link<T> {
        unsafe { (*self.inner.get()).children[dir as usize] }
    }

    #[inline]
    pub fn left(&self) -> Link<T> {
        self.child(Dir::Left)
    }

    #[inline]
    pub fn right(&self) -> Link<T> {
        self.child(Dir::Right)
    }

    #[inline]
    fn clear(&mut self) {
        self.set_parent(None);
        self.set_left(None);
        self.set_right(None);
        self.set_parity(false);
    }

    #[inline]
    fn set_parent(&mut self, parent: Link<T>) -> Link<T> {
        let inner = self.inner.get_mut();
        let old_parent = inner.parent_and_rank.ptr();
        inner.parent_and_rank.set_ptr(parent);
        old_parent
    }

    #[inline]
    fn set_child(&mut self, dir: Dir, child: Link<T>) -> Link<T> {
        mem::replace(&mut self.inner.get_mut().children[dir as usize], child)
    }

    #[inline]
    fn set_left(&mut self, left: Link<T>) -> Link<T> {
        self.set_child(Dir::Left, left)
    }

    #[inline]
    fn set_right(&mut self, right: Link<T>) -> Link<T> {
        self.set_child(Dir::Right, right)
    }

    #[inline]
    fn set_parity(&mut self, parity: bool) {
        self.inner.get_mut().parent_and_rank.set_parity(parity);
    }
}

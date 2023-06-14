//! An intrusive weak AVL tree, or WAVL tree.
//#![no_std]

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
// Corollaries:
// 3. All ancestors of a leaf have rank at least one.
//
//    Proof:
//    a. The parent of a leaf has rank 1 or 2 (by (1) and (2)).
//    b. All ancestors of a node have a rank greater than it (by (1)).
//    QED by (a) and (b)
//
// 4. All unary nodes are 1,2 with rank 1.
//
//    Proof:
//
//    Let `n` be a unary node.
//    a. `n` has one missing child with rank -1.
//    b. `r(n) ∈ {0, 1}` (by (1) and (a)).
//
//    Let `c` be `n`'s one child.
//    c. `r(c) ≥ 0` (by (2) and (3)).
//    c. `r(c) ∈ {-1, 0}` (by ())
//    d. `n`'s one child `c` has
//

use core::{
    cell::UnsafeCell, cmp::Ordering, fmt, marker::PhantomPinned, mem, ops::Not, pin::Pin,
    ptr::NonNull,
};
use std::borrow::Borrow;

use cordyceps::Linked;

pub trait TreeNode<L>: Linked<L> {
    type Key: Ord + fmt::Debug;

    fn key(&self) -> &Self::Key;
}

/// An intrusive weak AVL tree, or WAVL tree.
///
/// Implementation based on the paper [Rank-Balanced Trees] by Hauepler, Sen and Tarjan.
///
/// [Rank-Balanced Trees]: http://arks.princeton.edu/ark:/88435/pr1nz5z
pub struct WavlTree<T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    root: Link<T>,
    len: usize,
}

pub struct Links<T: ?Sized> {
    inner: UnsafeCell<LinksInner<T>>,
}

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
struct LinksInner<T: ?Sized> {
    parent: Link<T>,
    children: [Link<T>; 2],
    rank: i8,
    _unpin: PhantomPinned,
}

type Link<T> = Option<NonNull<T>>;

impl<T> WavlTree<T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    /// Returns a new empty tree.
    pub const fn new() -> WavlTree<T> {
        WavlTree { root: None, len: 0 }
    }

    /// Returns `true` if the map contains no elements.
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
            let rank = T::links(node).as_ref().rank();

            // Ensure all leaves have rank 0.
            if T::links(node).as_ref().is_leaf() {
                assert_eq!(rank, 0);
            }

            for child in [Dir::Left, Dir::Right] {
                if let Some(child) = T::links(node).as_ref().child(child) {
                    let child_rank = T::links(child).as_ref().rank();

                    // Ensure all rank differences are 1 or 2.
                    let rank_diff = rank - child_rank;
                    assert!([1, 2].contains(&rank_diff));

                    // Ensure child's parent link points to this node.
                    let parent = T::links(child)
                        .as_ref()
                        .parent()
                        .expect("left child parent pointer not set");
                    assert_eq!(node, parent);

                    self.assert_invariants_at(child);
                }
            }
        }
    }

    /// Returns a reference to the node corresponding to `key`.
    pub fn get<Q>(&self, key: &Q) -> Option<Pin<&T>>
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let ptr = self.get_raw(key)?;
        unsafe { Some(Pin::new_unchecked(ptr.as_ref())) }
    }

    fn get_raw<Q>(&self, key: &Q) -> Link<T>
    where
        T::Key: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let mut opt_cur = self.root;

        loop {
            let cur = opt_cur?;

            unsafe {
                match key.cmp(cur.as_ref().key().borrow()) {
                    Ordering::Less => opt_cur = T::links(cur).as_ref().left(),
                    Ordering::Equal => return Some(cur),
                    Ordering::Greater => opt_cur = T::links(cur).as_ref().right(),
                }
            }
        }
    }

    /// Returns the minimum element of the tree.
    pub fn first(&self) -> Option<Pin<&T>> {
        let mut opt_cur = self.root;

        unsafe {
            while let Some(cur) = opt_cur {
                opt_cur = T::links(cur).as_ref().left();
            }

            opt_cur.map(|first| Pin::new_unchecked(first.as_ref()))
        }
    }

    /// Returns the maximum element of the tree.
    pub fn last(&self) -> Option<Pin<&T>> {
        let mut opt_cur = self.root;

        unsafe {
            while let Some(cur) = opt_cur {
                opt_cur = T::links(cur).as_ref().right();
            }

            opt_cur.map(|first| Pin::new_unchecked(first.as_ref()))
        }
    }

    unsafe fn maybe_set_parent(&mut self, opt_node: Link<T>, parent: Link<T>) {
        let Some(node) = opt_node else {
            return;
        };

        unsafe { T::links(node).as_mut().set_parent(parent) };
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
            if T::links(parent).as_ref().child(Dir::Left) == Some(old_child) {
                T::links(parent).as_mut().set_child(Dir::Left, new_child);
            } else {
                T::links(parent).as_mut().set_child(Dir::Right, new_child);
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
            if T::links(parent).as_ref().child(Dir::Left) == Some(old_child) {
                if let Some(new_child) = new_child {
                    assert_ne!(
                        T::links(parent).as_ref().child(Dir::Right),
                        Some(new_child),
                        "`new_child` must not be a child of `parent`"
                    );
                }

                T::links(parent).as_mut().set_child(Dir::Left, new_child);
            } else if T::links(parent).as_ref().child(Dir::Right) == Some(old_child) {
                if let Some(new_child) = new_child {
                    assert_ne!(
                        T::links(parent).as_ref().child(Dir::Left),
                        Some(new_child),
                        "`new_child` must not be a child of `parent`"
                    );
                }

                T::links(parent).as_mut().set_child(Dir::Right, new_child);
            } else {
                unreachable!("`old_child` must be a child of `parent`");
            }

            if let Some(new_child) = new_child {
                T::links(new_child).as_mut().set_parent(Some(parent));
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
            let dir = if T::links(down).as_ref().right() == Some(up) {
                Dir::Left
            } else {
                Dir::Right
            };

            assert!(self.root.map(|r| r != up).unwrap_or(false));

            let across = T::links(up).as_ref().child(dir);
            T::links(down).as_mut().set_child(!dir, across);
            self.maybe_set_parent(across, Some(down));

            T::links(up).as_mut().set_child(dir, Some(down));
            let parent = T::links(down).as_mut().set_parent(Some(up));
            T::links(up).as_mut().set_parent(parent);

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
            let dir = if T::links(down_first).as_ref().right() == Some(up) {
                Dir::Right
            } else {
                Dir::Left
            };

            let across_first = T::links(up).as_ref().child(!dir);
            let across_second = T::links(up).as_ref().child(dir);

            self.maybe_set_parent(across_first, Some(down_first));

            T::links(down_first).as_mut().set_child(dir, across_first);
            T::links(down_first).as_mut().set_parent(Some(up));

            self.maybe_set_parent(across_second, Some(down_second));

            T::links(down_second)
                .as_mut()
                .set_child(!dir, across_second);
            let parent = T::links(down_second).as_mut().set_parent(Some(up));

            T::links(up).as_mut().set_parent(parent);
            T::links(up).as_mut().set_child(!dir, Some(down_first));
            T::links(up).as_mut().set_child(dir, Some(down_second));

            match parent {
                Some(parent) => self.replace_child(parent, down_second, Some(up)),
                None => self.root = Some(up),
            }
        }
    }

    fn sibling(&self, node: NonNull<T>) -> Link<T> {
        unsafe {
            let parent = T::links(node).as_ref().parent()?;

            if T::links(parent).as_ref().left() == Some(node) {
                T::links(parent).as_ref().right()
            } else {
                T::links(parent).as_ref().left()
            }
        }
    }

    /// Inserts an item into the tree.
    ///
    /// This operation completes in _O(log(n))_ time.
    pub fn insert(&mut self, item: T::Handle) {
        let ptr = T::into_ptr(item);

        let root = match self.root {
            Some(root) => root,
            None => {
                // Tree is empty. Set `item` as the root and return.
                unsafe {
                    let links = T::links(ptr).as_mut();
                    links.set_parent(None);
                    links.set_left(None);
                    links.set_right(None);
                }

                self.root = Some(ptr);
                self.len += 1;
                return;
            }
        };

        let mut parent_was_leaf = false;
        let mut opt_parent = Some(root);

        // Descend the tree, looking for a suitable leaf.
        while let Some(parent) = opt_parent {
            let ordering = unsafe { ptr.as_ref().key().cmp(parent.as_ref().key()) };

            let dir = match ordering {
                Ordering::Less => Dir::Left,
                Ordering::Equal => todo!(),
                Ordering::Greater => Dir::Right,
            };

            unsafe {
                let parent_links = T::links(parent).as_mut();
                match parent_links.child(dir) {
                    // Descend.
                    Some(child) => opt_parent = Some(child),

                    // Set `item` as child.
                    None => {
                        parent_was_leaf = parent_links.is_leaf();
                        parent_links.set_child(dir, Some(ptr));
                        T::links(ptr).as_mut().set_parent(Some(parent));
                        break;
                    }
                }
            }
        }

        if parent_was_leaf {
            // The parent node is rank 0 and the newly inserted node is also rank 0, which violates
            // the rank rule.
            self.rebalance_inserted(ptr);
        }

        self.len += 1;
    }

    // Performs a bottom-up rebalance of the tree after the insertion of `node`.
    //
    // Invariants:
    // - Both `node` and its parent are rank 0.
    // - `node` is not the tree root.
    // - `node` has no children and is thus rank 0 and 1,1.
    // - `node`'s parent is 0,1.
    fn rebalance_inserted(&mut self, node: NonNull<T>) {
        debug_assert_eq!(unsafe { T::links(node).as_ref().rank() }, 0);

        let mut x = node;
        let mut parent = unsafe {
            T::links(node)
                .as_ref()
                .parent()
                .expect("node must not be the tree root")
        };

        let mut x_rank = 0;
        let mut parent_rank = 0;
        let mut sibling_rank = -1;

        // While `x` is not the tree root and its parent is 0,1, promote the parent and ascend.
        while x_rank == parent_rank && x_rank == sibling_rank + 1 {
            unsafe {
                // Promote the parent.
                self.promote(parent);

                // Ascend one level. If this reaches the root, break.
                (parent, x) = match T::links(parent).as_mut().parent() {
                    Some(p) => (p, parent),
                    None => break,
                };

                x_rank = T::links(x).as_ref().rank();
                parent_rank = T::links(parent).as_ref().rank();
                sibling_rank = self
                    .sibling(x)
                    .map(|sib| T::links(sib).as_ref().rank())
                    .unwrap_or(-1);
            }
        }

        // If parent is not 0,2, the rank rule holds.
        if x_rank != parent_rank || x_rank != sibling_rank + 2 {
            return;
        }

        let z = parent;
        unsafe {
            let rotate_dir = if T::links(parent).as_ref().left() == Some(x) {
                Dir::Right
            } else {
                Dir::Left
            };

            let y = T::links(x).as_ref().child(rotate_dir);
            match y {
                Some(y) if T::links(y).as_ref().rank() == x_rank - 2 => {
                    self.rotate_at(parent, x);
                }

                None => {
                    self.rotate_at(parent, x);
                }

                Some(y) => {
                    debug_assert_eq!(x_rank - T::links(y).as_ref().rank(), 1);
                    self.rotate_twice_at(z, x, y);
                    self.promote(y);
                    self.demote(x);
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

        while let Some(left) = unsafe { T::links(cur).as_ref().left() } {
            parent = Some(cur);
            cur = left;
        }

        (cur, parent)
    }

    /// Removes an arbitrary node from the tree.
    ///
    /// # Safety
    ///
    /// It is the caller's responsibility to ensure that `node` is an element of `self`, and not any
    /// other tree.
    pub unsafe fn remove(&mut self, node: NonNull<T>) -> T::Handle {
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
        // [^1]: The successor of a node `a` is the least node in `a`'s right subtree.
        // [^2]: Unary nodes have rank 1 and are 1,2 by construction; the missing child has rank -1
        //       and is a 2-child, and the present child has rank 0 and is a 1-child. Thus the
        //       elevation (not promotion) of a unary 2-child's sole child always results in a
        //       3-child.

        let removed = node;

        unsafe {
            let parent = T::links(node).as_ref().parent();
            let left = T::links(node).as_ref().left();
            let right = T::links(node).as_ref().right();

            enum Violation<T: ?Sized> {
                None,
                ThreeChild(NonNull<T>, NonNull<T>),
                TwoTwoLeaf(Option<NonNull<T>>, NonNull<T>),
            }

            let violation = match (left, right) {
                (Some(left), Some(right)) => {
                    let (successor, successor_parent) = self.min_in_subtree(right);
                    let successor_right = T::links(successor).as_ref().right();

                    let successor_was_2_child =
                        self.is_2_child(successor_parent.unwrap_or(node), successor);

                    if let Some(successor_parent) = successor_parent {
                        // Elevate the successor's right child to replace it.
                        self.replace_child(successor_parent, successor, successor_right);
                        T::links(successor).as_mut().set_right(Some(right));
                        T::links(right).as_mut().set_parent(Some(successor));
                    }

                    self.replace_child_or_set_root(parent, node, Some(successor));

                    // Transfer rank of `node` to `successor`.
                    let node_rank = T::links(node).as_ref().rank();

                    T::links(successor).as_mut().set_parent(parent);
                    T::links(successor).as_mut().set_rank(node_rank);
                    T::links(successor).as_mut().set_left(Some(left));
                    // Right link is updated above iff succ != right.

                    T::links(left).as_mut().set_parent(Some(successor));

                    // If the successor has a right child and was a 2-child, its child becomes a
                    // 3-child; otherwise, if the successor is not `right`, and its parent is unary,
                    // its parent becomes a 2-2 leaf; otherwise the rank rule holds.
                    successor_right
                        .filter(|_| successor_was_2_child)
                        .map(|sr| Violation::ThreeChild(successor, sr))
                        .or_else(|| {
                            successor_parent
                                .filter(|&p| T::links(p).as_ref().is_leaf())
                                .map(|sp| Violation::TwoTwoLeaf(T::links(sp).as_ref().parent(), sp))
                        })
                        .unwrap_or(Violation::None)
                }

                (Some(child), None) | (None, Some(child)) => {
                    self.replace_child_or_set_root(parent, node, Some(child));
                    T::links(child).as_mut().set_parent(parent);

                    // The removed node was unary. Thus the removed node was 1,2, and its child was
                    // a 1-child. If the removed node was a 2-child, its child becomes a 3-child;
                    // otherwise the rank rule holds.

                    parent
                        .filter(|&p| {
                            T::links(p).as_ref().rank() - T::links(node).as_ref().rank() == 2
                        })
                        .map(|parent| Violation::ThreeChild(parent, node))
                        .unwrap_or(Violation::None)
                }

                (None, None) => {
                    self.replace_child_or_set_root(parent, node, None);

                    // The removed node was a leaf and thus 1,1. If its parent was unary, the parent
                    // becomes a 2,2 leaf; otherwise the rank rule holds.
                    parent
                        .filter(|&p| T::links(p).as_ref().is_leaf())
                        .map(|p| Violation::TwoTwoLeaf(T::links(p).as_ref().parent(), p))
                        .unwrap_or(Violation::None)
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
                        if self.is_3_child(parent, leaf) {
                            self.rebalance_3_child(parent, leaf);
                        }
                    }
                }
            }

            self.len -= 1;

            T::from_ptr(removed)
        }
    }

    unsafe fn rebalance_3_child(&mut self, mut parent: NonNull<T>, child: NonNull<T>) {
        let mut x = child;
        let mut y = self.sibling(x).unwrap();

        loop {
            if self.is_2_child(parent, y) {
                self.demote(parent);
            } else if self.is_2_2(y) {
                self.demote(y);
                self.demote(parent);
            } else {
                break;
            }

            x = parent;
            parent = T::links(x).as_ref().parent().expect("should have a parent");
            y = self.sibling(x).expect("should have a sibling");
        }

        if !self.is_3_child(parent, x) {
            return;
        }

        let dir = self.which_child(parent, x);

        // Here we give up on descriptive names entirely and just use the names from the paper.
        let z = parent;
        let v = T::links(y).as_ref().child(dir).unwrap();
        let w = T::links(y).as_ref().child(!dir).unwrap();

        if self.is_2_child(y, w) {
            self.rotate_twice_at(z, y, v);
            self.promote_twice(v);
            self.demote(y);
            self.demote_twice(z);
        } else {
            self.rotate_at(parent, y);
            self.promote(y);

            if T::links(z).as_ref().is_leaf() {
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
                let parent = parent.or_else(|| T::links(cur).as_ref().parent());

                let right = T::links(cur).as_ref().right();

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

        debug_assert!(self.root.is_none());
        debug_assert_eq!(self.len(), 0);
    }

    // Support methods ========================================================

    #[inline]
    unsafe fn promote(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.rank = inner.rank.checked_add(1).unwrap();
        }
    }

    #[inline]
    unsafe fn promote_twice(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.rank = inner.rank.checked_add(2).unwrap();
        }
    }

    #[inline]
    unsafe fn demote(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.rank = inner.rank.checked_sub(1).unwrap();
        }
    }

    #[inline]
    unsafe fn demote_twice(&mut self, node: NonNull<T>) {
        unsafe {
            let inner = T::links(node).as_mut().inner.get_mut();
            inner.rank = inner.rank.checked_sub(2).unwrap();
        }
    }

    /// Returns the rank of the pointed-to node.
    unsafe fn rank(&self, node: Option<NonNull<T>>) -> i8 {
        node.map(|n| T::links(n).as_ref().rank()).unwrap_or(-1)
    }

    unsafe fn is_2_2(&self, node: NonNull<T>) -> bool {
        unsafe {
            let left_rank = self.rank(T::links(node).as_ref().left());

            if left_rank != T::links(node).as_ref().rank() - 2 {
                return false;
            }

            let right_rank = self.rank(T::links(node).as_ref().right());

            left_rank == right_rank
        }
    }

    unsafe fn is_2_child(&self, parent: NonNull<T>, child: NonNull<T>) -> bool {
        unsafe { T::links(parent).as_ref().rank() == T::links(child).as_ref().rank() + 2 }
    }

    unsafe fn is_3_child(&self, parent: NonNull<T>, child: NonNull<T>) -> bool {
        unsafe { T::links(parent).as_ref().rank() == T::links(child).as_ref().rank() + 3 }
    }

    unsafe fn which_child(&self, parent: NonNull<T>, child: NonNull<T>) -> Dir {
        if T::links(parent).as_ref().left() == Some(child) {
            Dir::Left
        } else {
            Dir::Right
        }
    }
}

impl<T> Drop for WavlTree<T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T: ?Sized> Links<T> {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            inner: UnsafeCell::new(LinksInner {
                parent: None,
                children: [None; 2],
                rank: 0,
                _unpin: PhantomPinned,
            }),
        }
    }

    #[inline]
    fn is_leaf(&self) -> bool {
        self.left().is_none() && self.right().is_none()
    }

    #[inline]
    fn rank(&self) -> i8 {
        unsafe { (*self.inner.get()).rank }
    }

    #[inline]
    fn parent(&self) -> Link<T> {
        unsafe { (*self.inner.get()).parent }
    }

    #[inline]
    fn child(&self, dir: Dir) -> Link<T> {
        unsafe { (*self.inner.get()).children[dir as usize] }
    }

    #[inline]
    fn left(&self) -> Link<T> {
        self.child(Dir::Left)
    }

    #[inline]
    fn right(&self) -> Link<T> {
        self.child(Dir::Right)
    }

    #[inline]
    fn set_parent(&mut self, parent: Link<T>) -> Link<T> {
        mem::replace(&mut self.inner.get_mut().parent, parent)
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
    fn set_rank(&mut self, rank: i8) {
        self.inner.get_mut().rank = rank;
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::prelude::v1::*;

    use super::*;

    #[repr(C)]
    struct TestNode {
        links: Links<TestNode>,
        key: u32,
    }

    unsafe impl Linked<Links<TestNode>> for TestNode {
        type Handle = Box<TestNode>;

        fn into_ptr(r: Self::Handle) -> NonNull<Self> {
            NonNull::new(Box::into_raw(r)).unwrap()
        }

        unsafe fn from_ptr(ptr: NonNull<Self>) -> Self::Handle {
            unsafe { Box::from_raw(ptr.as_ptr()) }
        }

        unsafe fn links(ptr: NonNull<Self>) -> NonNull<Links<TestNode>> {
            // SAFETY: Self is #[repr(C)] and `links` is first field
            ptr.cast()
        }
    }

    impl TreeNode<Links<TestNode>> for TestNode {
        type Key = u32;

        fn key(&self) -> &Self::Key {
            &self.key
        }
    }

    fn insert_find_all(keys: &[u32]) {
        let mut tree: WavlTree<TestNode> = WavlTree::new();

        for &key in keys {
            tree.insert(Box::new(TestNode {
                links: Links::new(),
                key,
            }));
            tree.assert_invariants();
        }

        for key in keys {
            let node = tree.get_raw(key).expect("item not found");
            assert_eq!(unsafe { node.as_ref().key() }, key);
        }
    }

    #[test]
    fn zero_elems_find() {
        insert_find_all(&[]);
    }

    #[test]
    fn single_elem_find() {
        insert_find_all(&[0]);
    }

    #[test]
    fn two_elems_find() {
        insert_find_all(&[0, 1]);
        insert_find_all(&[1, 0]);
    }

    #[test]
    fn three_elems_find() {
        insert_find_all(&[0, 1, 2]);
        insert_find_all(&[0, 2, 1]);
        insert_find_all(&[1, 0, 2]);
        insert_find_all(&[1, 2, 0]);
        insert_find_all(&[2, 0, 1]);
        insert_find_all(&[2, 1, 0]);
    }

    #[test]
    fn four_elems_find() {
        insert_find_all(&[0, 1, 2, 3]);
        insert_find_all(&[0, 1, 3, 2]);
        insert_find_all(&[0, 2, 1, 3]);
        insert_find_all(&[0, 2, 3, 1]);
        insert_find_all(&[0, 3, 1, 2]);
        insert_find_all(&[0, 3, 2, 1]);

        insert_find_all(&[1, 0, 2, 3]);
        insert_find_all(&[1, 0, 3, 2]);
        insert_find_all(&[1, 2, 0, 3]);
        insert_find_all(&[1, 2, 3, 0]);
        insert_find_all(&[1, 3, 0, 2]);
        insert_find_all(&[1, 3, 2, 0]);

        insert_find_all(&[2, 0, 1, 3]);
        insert_find_all(&[2, 0, 3, 1]);
        insert_find_all(&[2, 1, 0, 3]);
        insert_find_all(&[2, 1, 3, 0]);
        insert_find_all(&[2, 3, 0, 1]);
        insert_find_all(&[2, 3, 1, 0]);

        insert_find_all(&[3, 0, 1, 2]);
        insert_find_all(&[3, 0, 2, 1]);
        insert_find_all(&[3, 1, 0, 2]);
        insert_find_all(&[3, 1, 2, 0]);
        insert_find_all(&[3, 2, 0, 1]);
        insert_find_all(&[3, 2, 1, 0]);
    }

    fn insert_remove_all(keys: &[u32]) {
        let mut tree: WavlTree<TestNode> = WavlTree::new();

        for &key in keys {
            tree.insert(Box::new(TestNode {
                links: Links::new(),
                key,
            }));
            tree.assert_invariants();
        }

        for key in keys {
            let node = tree.get_raw(key).expect("item not found");
            unsafe { tree.remove(node) };
            tree.assert_invariants();
        }

        for &key in keys {
            tree.insert(Box::new(TestNode {
                links: Links::new(),
                key,
            }));
            tree.assert_invariants();
        }

        for key in keys.iter().rev() {
            let node = tree.get_raw(key).expect("item not found");
            unsafe { tree.remove(node) };
            tree.assert_invariants();
        }
    }

    #[test]
    fn remove_one() {
        insert_remove_all(&[0]);
    }

    #[test]
    fn remove_two() {
        insert_remove_all(&[0, 1]);
        insert_remove_all(&[1, 0]);
    }

    #[test]
    fn remove_three() {
        insert_remove_all(&[0, 1, 2]);
        insert_remove_all(&[0, 2, 1]);
        insert_remove_all(&[1, 0, 2]);
        insert_remove_all(&[1, 2, 0]);
        insert_remove_all(&[2, 0, 1]);
        insert_remove_all(&[2, 1, 0]);
    }
}

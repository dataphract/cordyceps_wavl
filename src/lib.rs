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
    cell::UnsafeCell, cmp::Ordering, fmt, marker::PhantomData, marker::PhantomPinned, mem,
    ops::Not, pin::Pin, ptr::NonNull,
};

use cordyceps::Linked;

/// An intrusive weak AVL tree, or WAVL tree.
///
/// Implementation based on the paper [Rank-Balanced Trees] by Hauepler, Sen and Tarjan.
///
/// [Rank-Balanced Trees]: http://arks.princeton.edu/ark:/88435/pr1nz5z
pub struct WavlTree<T, K>
where
    T: Linked<Links<T, K>> + ?Sized,
    K: Ord + fmt::Debug,
{
    root: Link<T>,
    phantom: PhantomData<K>,
    len: usize,
}

pub struct Links<T: ?Sized, K: Ord> {
    inner: UnsafeCell<LinksInner<T, K>>,
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
struct LinksInner<T: ?Sized, K: Ord> {
    parent: Link<T>,
    children: [Link<T>; 2],
    key: K,
    rank: i8,
    _unpin: PhantomPinned,
}

type Link<T> = Option<NonNull<T>>;

impl<T, K> WavlTree<T, K>
where
    T: Linked<Links<T, K>> + ?Sized,
    K: Ord + fmt::Debug,
{
    /// Returns a new empty tree.
    pub const fn new() -> WavlTree<T, K> {
        WavlTree {
            root: None,
            phantom: PhantomData,
            len: 0,
        }
    }

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

    pub fn find(&self, item: &K) -> Option<Pin<&T>> {
        let ptr = self.find_raw(item)?;
        unsafe { Some(Pin::new_unchecked(ptr.as_ref())) }
    }

    fn find_raw(&self, item: &K) -> Link<T> {
        let mut opt_cur = self.root;

        loop {
            let cur = opt_cur?;

            unsafe {
                match item.cmp(T::links(cur).as_ref().key()) {
                    Ordering::Less => opt_cur = T::links(cur).as_ref().left(),
                    Ordering::Equal => return Some(cur),
                    Ordering::Greater => opt_cur = T::links(cur).as_ref().right(),
                }
            }
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

            println!("rotate {dir:?}");
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

    // Perform a bottom-up rebalance of the tree after the insertion of `node`.
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
                T::links(parent).as_mut().promote();

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
                    T::links(y).as_mut().promote();
                    T::links(x).as_mut().demote();
                }
            }

            // z is demoted in all cases.
            T::links(z).as_mut().demote();
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
            let ordering = unsafe {
                T::links(ptr)
                    .as_ref()
                    .key()
                    .cmp(T::links(parent).as_ref().key())
            };

            match ordering {
                Ordering::Less => unsafe {
                    let parent_links = T::links(parent).as_mut();
                    match parent_links.left() {
                        // Descend left.
                        Some(left) => opt_parent = Some(left),

                        // Set `item` as left child.
                        None => {
                            parent_was_leaf = parent_links.is_leaf();
                            parent_links.set_left(Some(ptr));
                            T::links(ptr).as_mut().set_parent(Some(parent));
                            break;
                        }
                    }
                },

                Ordering::Equal => todo!(),

                Ordering::Greater => unsafe {
                    let parent_links = T::links(parent).as_mut();
                    match parent_links.right() {
                        // Descend right.
                        Some(right) => opt_parent = Some(right),

                        // Set `item` as right child.
                        None => {
                            parent_was_leaf = parent_links.is_leaf();
                            parent_links.set_right(Some(ptr));
                            T::links(ptr).as_mut().set_parent(Some(parent));
                            break;
                        }
                    }
                },
            }
        }

        if parent_was_leaf {
            // The parent node is rank 0 and the newly inserted node is also rank 0, which violates
            // the rank rule.
            self.rebalance_inserted(ptr);
        }
    }

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

    unsafe fn rebalance_3_child(&mut self, mut parent: NonNull<T>, child: NonNull<T>) {
        let mut x = child;
        let mut y = self.sibling(x).unwrap();

        loop {
            if self.is_2_child(parent, y) {
                T::links(parent).as_mut().demote();
            } else if self.is_2_2(y) {
                T::links(y).as_mut().demote();
                T::links(parent).as_mut().demote();
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
            T::links(v).as_mut().promote_twice();
            T::links(y).as_mut().demote();
            T::links(z).as_mut().demote_twice();
        } else {
            self.rotate_at(parent, y);
            T::links(y).as_mut().promote();

            if T::links(z).as_ref().is_leaf() {
                T::links(z).as_mut().demote_twice();
            } else {
                T::links(z).as_mut().demote();
            }
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
        //    In this case `node`'s successor, `succ`, is removed from the tree and assumes `node`'s
        //    place and rank. The successor's right child is elevated to replace it.
        //
        //    The successor by definition has no left child[^1], so this can be treated as a removal
        //    of `succ` matching case 2 or 3.
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

        // This is the node being removed from the perspective of the caller.
        let caller_removed = node;

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
                    let (succ, succ_parent) = self.min_in_subtree(right);
                    let succ_right = T::links(succ).as_ref().right();

                    let succ_was_2_child = self.is_2_child(succ_parent.unwrap_or(node), succ);

                    // `succ_parent` is Some iff `succ` != `right`. `succ` still has a parent either
                    // way, it just might be `node`.
                    if let Some(succ_parent) = succ_parent {
                        // Elevate the successor's right child to replace it.
                        self.replace_child(succ_parent, succ, succ_right);
                        T::links(succ).as_mut().set_right(Some(right));
                        T::links(right).as_mut().set_parent(Some(succ));
                    }

                    // Link `succ` to `parent`.
                    self.replace_child_or_set_root(parent, node, Some(succ));

                    // Transfer rank of `node` to `succ`.
                    let node_rank = T::links(node).as_ref().rank();

                    T::links(succ).as_mut().set_parent(parent);
                    T::links(succ).as_mut().set_rank(node_rank);
                    T::links(succ).as_mut().set_left(Some(left));
                    // Right link is updated above iff succ != right.

                    // Link `succ` to `left`.
                    T::links(left).as_mut().set_parent(Some(succ));

                    // If the successor has a right child and was a 2-child, its child becomes a
                    // 3-child; otherwise, if the successor is not `right`, and its parent is unary,
                    // its parent becomes a 2-2 leaf; otherwise the rank rule holds.
                    succ_right
                        .filter(|_| succ_was_2_child)
                        .map(|sr| Violation::ThreeChild(succ, sr))
                        .or_else(|| {
                            succ_parent
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

                    // The removed node was a leaf and thus 1,1. If its parent is unary, the parent
                    // becomes a 2,2 leaf; otherwise the rank rule holds.
                    parent
                        .filter(|&p| T::links(p).as_ref().is_unary())
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
                    T::links(leaf).as_mut().demote();

                    if let Some(parent) = parent {
                        if self.is_3_child(parent, leaf) {
                            self.rebalance_3_child(parent, leaf);
                        }
                    }
                }
            }

            self.len -= 1;

            T::from_ptr(caller_removed)
        }
    }
}

impl<T, K> Drop for WavlTree<T, K>
where
    T: Linked<Links<T, K>> + ?Sized,
    K: Ord + fmt::Debug,
{
    fn drop(&mut self) {
        let mut opt_cur = self.root;

        while let Some(cur) = opt_cur {
            unsafe {
                println!("=== ITER ===");
                println!("cur = {:?}", T::links(cur).as_ref().key());

                // Descend to the minimum node.
                let (cur, parent) = self.min_in_subtree(cur);
                let parent = parent.or_else(|| T::links(cur).as_ref().parent());

                println!("min = {:?}", T::links(cur).as_ref().key());
                if let Some(parent) = parent {
                    println!("min_parent = {:?}", T::links(parent).as_ref().key());
                }

                let right = T::links(cur).as_ref().right();
                if let Some(right) = right {
                    println!("min_right = {:?}", T::links(right).as_ref().key());
                }

                // Elevate the node's right child (which may be None).
                self.replace_child_or_set_root(parent, cur, right);
                self.maybe_set_parent(right, parent);

                println!("  = AFTER RELINK");

                if let Some(parent_left) = parent.and_then(|p| T::links(p).as_ref().left()) {
                    println!(
                        "min_parent.left = {:?}",
                        T::links(parent_left).as_ref().key()
                    );
                };

                if let Some(right_parent) = right.and_then(|r| T::links(r).as_ref().parent()) {
                    println!(
                        "min_right.parent = {:?}",
                        T::links(right_parent).as_ref().key()
                    );
                }

                // Drop the node.
                drop(T::from_ptr(cur));

                // If the node had no right child, climb to the parent. If the node had no parent,
                // the tree is empty.
                opt_cur = right.or(parent);
            }
        }
    }
}

impl<T: ?Sized, K: Ord> Links<T, K> {
    #[must_use]
    pub const fn new(key: K) -> Self {
        Self {
            inner: UnsafeCell::new(LinksInner {
                parent: None,
                children: [None; 2],
                key,
                rank: 0,
                _unpin: PhantomPinned,
            }),
        }
    }

    #[inline]
    fn is_unary(&self) -> bool {
        self.left().is_some() != self.right().is_some()
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
    fn key(&self) -> &K {
        unsafe { &(*self.inner.get()).key }
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

    #[inline]
    fn promote(&mut self) {
        let inner = self.inner.get_mut();
        inner.rank = inner.rank.checked_add(1).unwrap();
    }

    #[inline]
    fn promote_twice(&mut self) {
        let inner = self.inner.get_mut();
        inner.rank = inner.rank.checked_add(2).unwrap();
    }

    #[inline]
    fn demote(&mut self) {
        let inner = self.inner.get_mut();
        assert!(inner.rank > 0);
        inner.rank = inner.rank.checked_sub(1).unwrap();
    }

    #[inline]
    fn demote_twice(&mut self) {
        let inner = self.inner.get_mut();
        assert!(inner.rank > 1);
        inner.rank = inner.rank.checked_sub(2).unwrap();
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::prelude::v1::*;

    use super::*;

    #[repr(C)]
    struct TestNode {
        links: Links<TestNode, u32>,
    }

    unsafe impl Linked<Links<TestNode, u32>> for TestNode {
        type Handle = Box<TestNode>;

        fn into_ptr(r: Self::Handle) -> NonNull<Self> {
            NonNull::new(Box::into_raw(r)).unwrap()
        }

        unsafe fn from_ptr(ptr: NonNull<Self>) -> Self::Handle {
            unsafe { Box::from_raw(ptr.as_ptr()) }
        }

        unsafe fn links(ptr: NonNull<Self>) -> NonNull<Links<TestNode, u32>> {
            // SAFETY: Self is #[repr(C)] and `links` is first field
            ptr.cast()
        }
    }

    fn insert_find_all(keys: &[u32]) {
        let mut tree: WavlTree<TestNode, u32> = WavlTree::new();

        for &key in keys {
            tree.insert(Box::new(TestNode {
                links: Links::new(key),
            }));
            tree.assert_invariants();
        }

        for key in keys {
            let node = tree.find_raw(key).expect("item not found");
            assert_eq!(unsafe { TestNode::links(node).as_ref().key() }, key);
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
        let mut tree: WavlTree<TestNode, u32> = WavlTree::new();

        for &key in keys {
            tree.insert(Box::new(TestNode {
                links: Links::new(key),
            }));
            tree.assert_invariants();
        }

        for key in keys {
            let node = tree.find_raw(key).expect("item not found");
            unsafe { tree.remove(node) };
        }
    }

    #[test]
    fn remove_one() {
        insert_remove_all(&[0]);
    }
}
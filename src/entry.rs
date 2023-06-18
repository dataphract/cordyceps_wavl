#![allow(dead_code)]

use core::{borrow::Borrow, pin::Pin, ptr::NonNull};

use crate::{Dir, Links, TreeNode, WavlTree};

/// A view into a single entry in a [`WavlTree`], which may be either vacant or occupied.
pub enum Entry<'tree, 'key, T, Q>
where
    T: TreeNode<Links<T>> + ?Sized,
    T::Key: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    Vacant(VacantEntry<'tree, 'key, T, Q>),
    Occupied(OccupiedEntry<'tree, T>),
}

impl<'tree, 'key, T, Q> Entry<'tree, 'key, T, Q>
where
    T: TreeNode<Links<T>> + ?Sized,
    T::Key: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    pub(crate) unsafe fn vacant_root(tree: &'tree mut WavlTree<T>, key: &'key Q) -> Self {
        Entry::Vacant(VacantEntry {
            tree,
            key,
            insert_as: InsertAs::Root,
        })
    }

    pub(crate) unsafe fn vacant_child(
        tree: &'tree mut WavlTree<T>,
        key: &'key Q,
        parent: NonNull<T>,
        dir: Dir,
    ) -> Self {
        Entry::Vacant(VacantEntry {
            tree,
            key,
            insert_as: InsertAs::Child { parent, dir },
        })
    }

    pub(crate) unsafe fn occupied(tree: &'tree mut WavlTree<T>, node: NonNull<T>) -> Self {
        Entry::Occupied(OccupiedEntry { tree, node })
    }
}

pub(crate) enum InsertAs<T: ?Sized> {
    Root,
    Child { parent: NonNull<T>, dir: Dir },
}

pub struct VacantEntry<'tree, 'key, T, Q>
where
    T: TreeNode<Links<T>> + ?Sized,
    T::Key: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    pub(crate) tree: &'tree mut WavlTree<T>,
    pub(crate) key: &'key Q,
    pub(crate) insert_as: InsertAs<T>,
}

impl<'tree, 'key, T, Q> VacantEntry<'tree, 'key, T, Q>
where
    T: TreeNode<Links<T>> + ?Sized,
    T::Key: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    /// Inserts `item` at the key associated with this entry.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the key returned by `item.key()` is equal to the key used to
    /// retrieve this entry.
    pub unsafe fn insert(self, item: T::Handle) -> Pin<&'tree mut T> {
        let mut ptr = T::into_ptr(item);

        unsafe {
            match self.insert_as {
                InsertAs::Root => self.tree.insert_as_root(ptr),
                InsertAs::Child { parent, dir } => self.tree.insert_as_child(parent, dir, ptr),
            }
        }

        Pin::new_unchecked(ptr.as_mut())
    }
}

pub struct OccupiedEntry<'tree, T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    pub(crate) tree: &'tree mut WavlTree<T>,
    pub(crate) node: NonNull<T>,
}

impl<'tree, T> OccupiedEntry<'tree, T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    /// Returns a reference to the item in the entry.
    pub fn get(&self) -> &'tree T {
        // SAFETY: `self.tree` is mutably borrowed for `'tree`
        unsafe { self.node.as_ref() }
    }

    /// Returns a pinned mutable reference to the item in the entry.
    ///
    /// # Safety
    ///
    /// The caller must ensure that neither the links nor the key of the mutably borrowed item are
    /// modified, as doing so may result in undefined behavior.
    pub unsafe fn get_mut(&mut self) -> Pin<&'tree mut T> {
        // SAFETY: `self.tree` is mutably borrowed for `'tree`, and `self.node` is guaranteed pinned
        // by contract with `Linked`.
        unsafe { Pin::new_unchecked(self.node.as_mut()) }
    }

    /// Inserts a new item into the entry, returning the previous item.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `item`'s key is equivalent to the key of the existing item.
    pub unsafe fn insert(&mut self, item: T::Handle) -> T::Handle {
        let new_ptr = T::into_ptr(item);
        let old_ptr = self.node;

        // Point this entry at the new item.
        self.node = new_ptr;

        unsafe {
            // Read the old value's links.
            let old_links = self.tree.links(old_ptr);
            let rank = old_links.rank();
            let parent = old_links.parent();
            let left = old_links.left();
            let right = old_links.right();

            // Link the new item into the tree.
            if let Some(parent) = parent {
                let which = self.tree.which_child(parent, Some(old_ptr));
                self.tree.links_mut(parent).set_child(which, Some(new_ptr));
            }

            if let Some(left) = left {
                self.tree.links_mut(left).set_parent(Some(new_ptr));
            }

            if let Some(right) = right {
                self.tree.links_mut(right).set_parent(Some(new_ptr));
            }

            self.tree.links_mut(new_ptr).set_parent(parent);
            self.tree.links_mut(new_ptr).set_left(left);
            self.tree.links_mut(new_ptr).set_right(right);
            self.tree.links_mut(new_ptr).set_rank(rank);

            // Deinit the old item's links.
            self.tree.links_mut(old_ptr).clear();

            self.tree.len += 1;

            T::from_ptr(old_ptr)
        }
    }

    /// Removes and returns the item pointed to by this entry.
    pub fn remove(self) -> T::Handle {
        unsafe { self.tree.remove_at(self.node) }
    }
}

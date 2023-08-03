use core::{marker::PhantomData, pin::Pin, ptr::NonNull};

use crate::{Links, TreeNode, WavlTree};

/// A cursor over a [`WavlTree`].
///
/// A cursor points either to an element of the tree or to a "ghost" non-element that connects the
/// last element to the first.
pub struct Cursor<'tree, T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    curs: CursorRaw<T>,
    phantom: PhantomData<&'tree WavlTree<T>>,
}

impl<'tree, T> Cursor<'tree, T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    pub(crate) fn first(tree: &'tree WavlTree<T>) -> Cursor<'tree, T> {
        Cursor {
            curs: CursorRaw::first(tree.into()),
            phantom: PhantomData,
        }
    }

    pub(crate) fn last(tree: &'tree WavlTree<T>) -> Cursor<'tree, T> {
        Cursor {
            curs: CursorRaw::last(tree.into()),
            phantom: PhantomData,
        }
    }

    /// Moves the cursor to the next element of the `WavlTree`.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method moves it to the first
    /// element. If it is pointing to the last element, this method moves it to the "ghost"
    /// non-element.
    pub fn move_next(&mut self) {
        unsafe { self.curs.move_next() }
    }

    /// Moves the cursor to the previous element of the `WavlTree`.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method moves it to the last
    /// element. If it is pointing to the first element, this method moves it to the "ghost"
    /// non-element.
    pub fn move_prev(&mut self) {
        unsafe { self.curs.move_prev() }
    }

    /// Returns a reference to the item pointed to by the cursor.
    ///
    /// This returns `None` if the cursor is currently pointing to the "ghost" non-element.
    pub fn get(&self) -> Option<&T> {
        unsafe { self.curs.get() }
    }

    /// Returns a reference to the next item.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method returns the first element.
    /// If it is pointing to the last element, this method returns `None`.
    pub fn peek_next(&self) -> Option<&T> {
        unsafe { self.curs.peek_next() }
    }

    /// Returns a reference to the previous item.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method returns the last element.
    /// If it is pointing to the first element, this method returns `None`.
    pub fn peek_prev(&self) -> Option<&T> {
        unsafe { self.curs.peek_prev() }
    }
}

/// A cursor over a [`WavlTree`] which supports editing operations.
///
/// A cursor points either to an element of the tree or to a "ghost" non-element that connects the
/// last element to the first.
pub struct CursorMut<'tree, T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    curs: CursorRaw<T>,
    phantom: PhantomData<&'tree mut WavlTree<T>>,
}

impl<'tree, T> CursorMut<'tree, T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    pub(crate) fn first(tree: &'tree mut WavlTree<T>) -> CursorMut<'tree, T> {
        CursorMut {
            curs: CursorRaw::first(tree.into()),
            phantom: PhantomData,
        }
    }

    pub(crate) fn last(tree: &'tree mut WavlTree<T>) -> CursorMut<'tree, T> {
        CursorMut {
            curs: CursorRaw::last(tree.into()),
            phantom: PhantomData,
        }
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The `CursorMut` remains immutably borrowed for the lifetime of the returned `Cursor`.
    pub fn as_cursor(&self) -> Cursor<'_, T> {
        Cursor {
            curs: CursorRaw {
                tree: self.curs.tree,
                ptr: self.curs.ptr,
            },
            phantom: PhantomData,
        }
    }

    /// Moves the cursor to the next element of the `WavlTree`.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method will move it to the first
    /// element. If it is pointing to the last element, this method will move it to the "ghost"
    /// non-element.
    pub fn move_next(&mut self) {
        unsafe { self.curs.move_next() }
    }

    /// Moves the cursor to the previous element of the `WavlTree`.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method will move it to the last
    /// element. If it is pointing to the first element, this method will move it to the "ghost"
    /// non-element.
    pub fn move_prev(&mut self) {
        unsafe { self.curs.move_prev() }
    }

    /// Returns a reference to the item pointed to by the cursor.
    ///
    /// This returns `None` if the cursor is currently pointing to the "ghost" non-element.
    pub fn get(&self) -> Option<&T> {
        unsafe { self.curs.get() }
    }

    /// Returns a pinned mutable reference to the item pointed to by the cursor.
    ///
    /// This returns `None` if the cursor is currently pointing to the "ghost" non-element.
    ///
    /// # Safety
    ///
    /// The caller must ensure that modifications to the returned value do not violate the
    /// invariants of the tree. In particular, the result of comparisons between the key of the
    /// returned item and the keys of other items in the tree must not change.
    pub unsafe fn get_mut(&mut self) -> Option<Pin<&mut T>> {
        unsafe { self.curs.get_mut() }
    }

    /// Returns a reference to the next item.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method returns the first element.
    /// If it is pointing to the last element, this method returns `None`.
    pub fn peek_next(&self) -> Option<&T> {
        unsafe { self.curs.peek_next() }
    }

    /// Returns a reference to the previous item.
    ///
    /// If the cursor is pointing to the "ghost" non-element, this method returns the last element.
    /// If it is pointing to the first element, this method returns `None`.
    pub fn peek_prev(&self) -> Option<&T> {
        unsafe { self.curs.peek_prev() }
    }

    /// Removes the current element from the tree.
    ///
    /// This returns the removed element and moves the cursor to the next element. If the cursor is
    /// pointing to the "ghost" non-element, this method returns `None`, and neither the tree nor
    /// the cursor is modified.
    pub fn remove_current(&mut self) -> Option<T::Handle> {
        unsafe { self.curs.remove_current() }
    }

    /// Removes the current element from the tree.
    ///
    /// This returns the removed element and moves the cursor to the previous element. If the cursor is
    /// pointing to the "ghost" non-element, this method returns `None`, and neither the tree nor
    /// the cursor is modified.
    pub fn remove_current_and_move_prev(&mut self) -> Option<T::Handle> {
        unsafe { self.curs.remove_current_and_move_prev() }
    }
}

struct CursorRaw<T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    tree: NonNull<WavlTree<T>>,
    ptr: Option<NonNull<T>>,
}

impl<T> CursorRaw<T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    fn first(tree: NonNull<WavlTree<T>>) -> CursorRaw<T> {
        CursorRaw {
            tree,
            ptr: unsafe { tree.as_ref().first },
        }
    }

    fn last(tree: NonNull<WavlTree<T>>) -> CursorRaw<T> {
        CursorRaw {
            tree,
            ptr: unsafe { tree.as_ref().last },
        }
    }

    unsafe fn move_next(&mut self) {
        let tree = unsafe { self.tree.as_ref() };

        match self.ptr {
            Some(p) => self.ptr = unsafe { tree.successor_raw(p) },
            None => self.ptr = tree.first,
        }
    }

    unsafe fn move_prev(&mut self) {
        let tree = unsafe { self.tree.as_ref() };

        match self.ptr {
            Some(p) => self.ptr = unsafe { tree.predecessor_raw(p) },
            None => self.ptr = tree.last,
        }
    }

    unsafe fn get(&self) -> Option<&T> {
        self.ptr.map(|p| unsafe { p.as_ref() })
    }

    unsafe fn get_mut(&mut self) -> Option<Pin<&mut T>> {
        self.ptr
            .map(|mut p| unsafe { Pin::new_unchecked(p.as_mut()) })
    }

    unsafe fn peek_next(&self) -> Option<&T> {
        let tree = unsafe { self.tree.as_ref() };

        let next_ptr = match self.ptr {
            Some(p) => tree.successor_raw(p),
            None => tree.first,
        };

        next_ptr.map(|p| unsafe { p.as_ref() })
    }

    unsafe fn peek_prev(&self) -> Option<&T> {
        let tree = unsafe { self.tree.as_ref() };

        let prev_ptr = match self.ptr {
            Some(p) => tree.predecessor_raw(p),
            None => tree.last,
        };

        prev_ptr.map(|p| unsafe { p.as_ref() })
    }

    unsafe fn remove_current(&mut self) -> Option<T::Handle> {
        let remove = self.ptr?;

        self.move_next();

        let tree = unsafe { self.tree.as_mut() };
        Some(tree.remove_at(remove))
    }

    unsafe fn remove_current_and_move_prev(&mut self) -> Option<T::Handle> {
        let remove = self.ptr?;

        self.move_prev();

        let tree = unsafe { self.tree.as_mut() };
        Some(tree.remove_at(remove))
    }
}

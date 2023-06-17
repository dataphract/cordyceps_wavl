use core::{marker::PhantomData, pin::Pin, ptr::NonNull};

use crate::{Dir, Link, Links, TreeNode, WavlTree};

#[derive(Debug)]
enum CameFrom {
    Parent,
    PreChild,
    Here,
    PostChild,
}

/// An iterator over the items in a [`WavlTree`] in sorted order.
///
/// This struct is created via [`WavlTree::iter`].
pub struct Iter<'tree, T: TreeNode<Links<T>> + ?Sized> {
    inner: IterRaw<T>,
    phantom: PhantomData<&'tree WavlTree<T>>,
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iter<'tree, T> {
    pub(crate) fn new(tree: &'tree WavlTree<T>) -> Self {
        Iter {
            inner: IterRaw::new(tree),
            phantom: PhantomData,
        }
    }
}

pub struct IterMut<'tree, T: TreeNode<Links<T>> + ?Sized> {
    inner: IterRaw<T>,
    phantom: PhantomData<&'tree mut WavlTree<T>>,
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> IterMut<'tree, T> {
    pub(crate) fn new(tree: &'tree mut WavlTree<T>) -> Self {
        IterMut {
            inner: IterRaw::new_mut(tree),
            phantom: PhantomData,
        }
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iterator for Iter<'tree, T> {
    type Item = &'tree T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next_either(Dir::Left)
            // SAFETY: Shared references can be safely returned without pinning, as the
            // reference cannot be moved out of. See the docs for `Pin::get_ref`.
            .map(|ptr| unsafe { ptr.as_ref() })
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> DoubleEndedIterator for Iter<'tree, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_either(Dir::Right)
            // SAFETY: See note above for `<Iter as Iterator>::next`.
            .map(|ptr| unsafe { ptr.as_ref() })
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iterator for IterMut<'tree, T> {
    type Item = Pin<&'tree mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next_either(Dir::Left)
            // SAFETY: values of type `T` are guaranteed pinned by contract with `cordyceps::Linked`.
            .map(|mut ptr| unsafe { Pin::new_unchecked(ptr.as_mut()) })
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> DoubleEndedIterator for IterMut<'tree, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner
            .next_either(Dir::Right)
            // SAFETY: values of type `T` are guaranteed pinned by contract with `cordyceps::Linked`.
            .map(|mut ptr| unsafe { Pin::new_unchecked(ptr.as_mut()) })
    }
}

struct IterRaw<T: TreeNode<Links<T>> + ?Sized> {
    tree: NonNull<WavlTree<T>>,

    cur: [Link<T>; 2],
    from: [CameFrom; 2],

    len: usize,
}

impl<T: TreeNode<Links<T>> + ?Sized> IterRaw<T> {
    fn new(tree: &WavlTree<T>) -> Self {
        IterRaw {
            tree: tree.into(),

            cur: [tree.root, tree.root],
            from: [CameFrom::Parent, CameFrom::Parent],
            len: tree.len(),
        }
    }

    fn new_mut(tree: &mut WavlTree<T>) -> Self {
        IterRaw {
            tree: tree.into(),

            cur: [tree.root, tree.root],
            from: [CameFrom::Parent, CameFrom::Parent],
            len: tree.len(),
        }
    }

    fn next_either(&mut self, dir: Dir) -> Option<NonNull<T>> {
        if self.len == 0 {
            return None;
        }

        let mut cur = self.cur[dir as usize]?;

        loop {
            match self.from[dir as usize] {
                CameFrom::Parent => {
                    // Upon entering a new subtree, find the {minimum,maximum} element.
                    while let Some(pre_child) = unsafe { T::links(cur).as_ref().child(dir) } {
                        cur = pre_child;
                    }

                    // Once the {minimum,maximum} is found, its (empty) {left,right} subtree has been exhausted.
                    self.from[dir as usize] = CameFrom::PreChild;
                }

                CameFrom::PreChild => {
                    // The {left,right} subtree has been exhausted, so this node is up next. Save off the
                    // iterator state and return it.
                    self.cur[dir as usize] = Some(cur);
                    self.from[dir as usize] = CameFrom::Here;
                    self.len -= 1;

                    return Some(cur);
                }

                CameFrom::Here => {
                    // The current node was just yielded.
                    if let Some(post_child) = unsafe { T::links(cur).as_ref().child(!dir) } {
                        // If the {right,left} subtree is not empty, go there.
                        self.from[dir as usize] = CameFrom::Parent;

                        cur = post_child;
                    } else if let Some(parent) = unsafe { T::links(cur).as_ref().parent() } {
                        // Otherwise, ascend one level.
                        self.from[dir as usize] =
                            match unsafe { self.tree.as_ref().which_child(parent, Some(cur)) } {
                                d if d == dir => CameFrom::PreChild,
                                _ => CameFrom::PostChild,
                            };

                        cur = parent;
                    } else {
                        unreachable!()
                    }
                }

                CameFrom::PostChild => {
                    // Ascend until we find the successor element.
                    while let Some(parent) = unsafe { T::links(cur).as_ref().parent() } {
                        let which_child =
                            unsafe { self.tree.as_ref().which_child(parent, Some(cur)) };
                        cur = parent;

                        if which_child == dir {
                            break;
                        }
                    }

                    self.cur[dir as usize] = Some(cur);
                    self.from[dir as usize] = CameFrom::PreChild;
                }
            }
        }
    }
}

use crate::{Dir, Link, Links, TreeNode, WavlTree};

enum CameFrom {
    Parent,
    LeftChild,
    Here,
    RightChild,
}

pub struct Iter<'tree, T: TreeNode<Links<T>> + ?Sized> {
    tree: &'tree WavlTree<T>,

    front_cur: Link<T>,
    front_from: CameFrom,

    len: usize,
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iter<'tree, T> {
    pub(crate) fn new(tree: &'tree WavlTree<T>) -> Self {
        Iter {
            tree,

            front_cur: tree.root,
            front_from: CameFrom::Parent,
            len: tree.len(),
        }
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iterator for Iter<'tree, T> {
    type Item = &'tree T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let mut cur = self.front_cur?;

        loop {
            match self.front_from {
                CameFrom::Parent => {
                    // Upon entering a new subtree, find the minimum element.
                    while let Some(left) = unsafe { T::links(cur).as_ref().left() } {
                        cur = left;
                    }

                    // Once the minimum is found, its (empty) left subtree has been exhausted.
                    self.front_from = CameFrom::LeftChild;
                }

                CameFrom::LeftChild => {
                    // The left subtree has been exhausted, so this node is up next. Save off the
                    // iterator state and return it.
                    self.front_cur = Some(cur);
                    self.front_from = CameFrom::Here;
                    self.len -= 1;

                    return Some(unsafe { cur.as_ref() });
                }

                CameFrom::Here => {
                    // The current node was just yielded.
                    if let Some(right) = unsafe { T::links(cur).as_ref().right() } {
                        // If the right subtree is not empty, go there.
                        self.front_from = CameFrom::Parent;

                        cur = right;
                    } else if let Some(parent) = unsafe { T::links(cur).as_ref().parent() } {
                        // Otherwise, ascend one level.
                        self.front_from = match unsafe { self.tree.which_child(parent, Some(cur)) }
                        {
                            Dir::Left => CameFrom::LeftChild,
                            Dir::Right => CameFrom::RightChild,
                        };

                        cur = parent;
                    } else {
                        unreachable!()
                    }
                }

                CameFrom::RightChild => {
                    // Ascend until we find the successor element.
                    while let Some(parent) = unsafe { T::links(cur).as_ref().parent() } {
                        match unsafe { self.tree.which_child(parent, Some(cur)) } {
                            Dir::Left => break,
                            Dir::Right => cur = parent,
                        }
                    }

                    self.front_cur = Some(cur);
                    self.front_from = CameFrom::LeftChild;
                }
            }
        }
    }
}

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
    tree: &'tree WavlTree<T>,

    cur: [Link<T>; 2],
    from: [CameFrom; 2],

    len: usize,
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iter<'tree, T> {
    pub(crate) fn new(tree: &'tree WavlTree<T>) -> Self {
        Iter {
            tree,

            cur: [tree.root, tree.root],
            from: [CameFrom::Parent, CameFrom::Parent],
            len: tree.len(),
        }
    }
}

fn next_either<'tree, T>(it: &mut Iter<'tree, T>, dir: Dir) -> Option<&'tree T>
where
    T: TreeNode<Links<T>> + ?Sized,
{
    if it.len == 0 {
        return None;
    }

    let mut cur = it.cur[dir as usize]?;

    loop {
        println!("{:?}", it.from[dir as usize]);
        match it.from[dir as usize] {
            CameFrom::Parent => {
                // Upon entering a new subtree, find the {minimum,maximum} element.
                while let Some(pre_child) = unsafe { T::links(cur).as_ref().child(dir) } {
                    cur = pre_child;
                }

                // Once the {minimum,maximum} is found, its (empty) {left,right} subtree has been exhausted.
                it.from[dir as usize] = CameFrom::PreChild;
            }

            CameFrom::PreChild => {
                // The {left,right} subtree has been exhausted, so this node is up next. Save off the
                // iterator state and return it.
                it.cur[dir as usize] = Some(cur);
                it.from[dir as usize] = CameFrom::Here;
                it.len -= 1;
                println!("---");

                return Some(unsafe { cur.as_ref() });
            }

            CameFrom::Here => {
                // The current node was just yielded.
                if let Some(post_child) = unsafe { T::links(cur).as_ref().child(!dir) } {
                    // If the {right,left} subtree is not empty, go there.
                    it.from[dir as usize] = CameFrom::Parent;

                    cur = post_child;
                } else if let Some(parent) = unsafe { T::links(cur).as_ref().parent() } {
                    // Otherwise, ascend one level.
                    it.from[dir as usize] = match unsafe { it.tree.which_child(parent, Some(cur)) }
                    {
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
                    cur = parent;
                    if unsafe { it.tree.which_child(parent, Some(cur)) } == dir {
                        break;
                    }
                }

                it.cur[dir as usize] = Some(cur);
                it.from[dir as usize] = CameFrom::PreChild;
            }
        }
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> Iterator for Iter<'tree, T> {
    type Item = &'tree T;

    fn next(&mut self) -> Option<Self::Item> {
        next_either(self, Dir::Left)
    }
}

impl<'tree, T: TreeNode<Links<T>> + ?Sized> DoubleEndedIterator for Iter<'tree, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        next_either(self, Dir::Right)
    }
}

extern crate std;

use core::ptr::NonNull;
use std::{collections::VecDeque, fmt, prelude::v1::*};

use crate::{Links, TreeNode, WavlTree};

impl<T> WavlTree<T>
where
    T: TreeNode<Links<T>>,
{
    pub fn dotgraph<'a, W, K>(&'a self, name: &str, mut w: W) -> fmt::Result
    where
        W: fmt::Write,
        K: fmt::Display + From<&'a T::Key>,
    {
        let root = match self.root {
            Some(r) => r,
            None => return write!(w, "digraph \"graph-{name}\" {{}}"),
        };

        enum Item<T: TreeNode<Links<T>>> {
            Node(NonNull<T>),
            Missing(u32),
        }

        let mut queue = VecDeque::new();
        queue.push_back(Item::Node(root));

        write!(
            w,
            "digraph \"graph-{name}\" {{\n subgraph \"subgraph-{name}\" {{"
        )?;

        let mut missing = 0;
        let mut links = String::new();

        for _rank in 0.. {
            use fmt::Write;
            let remaining = queue.len();
            if remaining == 0 {
                break;
            }

            write!(w, "{{rank=same; ")?;

            for _rank_node in 0..remaining {
                let node = queue.pop_front().unwrap();

                let node = match node {
                    Item::Node(node) => node,
                    Item::Missing(id) => {
                        write!(w, "\"graph{name}-missing{id}\" [shape=point]; ")?;
                        continue;
                    }
                };

                let key: K = unsafe { node.as_ref().key().into() };
                let parity = unsafe { T::links(node).as_ref().parity() } as usize;
                write!(w, "\"graph{name}-{key}\" [label=\"{key}:{parity:?}\"]; ")?;

                if let Some(left) = unsafe { self.links(node).left() } {
                    let child_key: K = unsafe { left.as_ref().key().into() };

                    queue.push_back(Item::Node(left));
                    writeln!(
                        links,
                        "\"graph{name}-{key}\" -> \"graph{name}-{child_key}\";"
                    )?;
                } else {
                    queue.push_back(Item::Missing(missing));
                    writeln!(
                        links,
                        "\"graph{name}-{key}\" -> \"graph{name}-missing{missing}\";"
                    )?;
                    missing += 1;
                }

                if let Some(right) = unsafe { self.links(node).right() } {
                    let child_key: K = unsafe { right.as_ref().key().into() };

                    queue.push_back(Item::Node(right));
                    writeln!(
                        links,
                        "\"graph{name}-{key}\" -> \"graph{name}-{child_key}\";"
                    )?;
                } else {
                    queue.push_back(Item::Missing(missing));
                    writeln!(
                        links,
                        "\"graph{name}-{key}\" -> \"graph{name}-missing{missing}\";"
                    )?;
                    missing += 1;
                }
            }

            writeln!(w, "}}")?;
        }

        w.write_str(&links)?;

        w.write_str(" }\n}")
    }
}

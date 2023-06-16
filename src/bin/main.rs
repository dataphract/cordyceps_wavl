use std::ptr::NonNull;

use cordyceps::Linked;
use cordyceps_wavl::{Links, TreeNode, WavlTree};

#[derive(Debug)]
#[repr(C)]
struct TestNode {
    links: Links<TestNode>,
    key: u32,
}

impl TestNode {
    fn new(key: u32) -> Box<TestNode> {
        Box::new(TestNode {
            links: Links::new(),
            key,
        })
    }
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

fn main() {
    let mut tree: WavlTree<TestNode> = WavlTree::new();

    tree.insert(TestNode::new(2));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(0));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(3));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(4));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(5));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(1));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(6));
    tree.assert_invariants();
    println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    let zero = tree.pop_first().unwrap().key;
    assert_eq!(zero, 0);
    tree.assert_invariants();

    drop(tree);
}

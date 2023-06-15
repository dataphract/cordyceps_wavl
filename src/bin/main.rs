use std::ptr::NonNull;

use cordyceps::Linked;
use cordyceps_wavl::{Links, TreeNode, WavlTree};

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

fn main() {
    let mut tree: WavlTree<TestNode> = WavlTree::new();

    tree.insert(Box::new(TestNode {
        links: Links::new(),
        key: 0,
    }));

    tree.insert(Box::new(TestNode {
        links: Links::new(),
        key: 2,
    }));

    tree.insert(Box::new(TestNode {
        links: Links::new(),
        key: 1,
    }));

    tree.insert(Box::new(TestNode {
        links: Links::new(),
        key: 3,
    }));

    for elem in tree.iter() {
        println!("key: {}", elem.key);
    }

    let node = tree.get(&0).expect("item not found");
    unsafe { tree.remove(node.get_ref().into()) };
    tree.assert_invariants();

    let node = tree.get(&2).expect("item not found");
    unsafe { tree.remove(node.get_ref().into()) };
    tree.assert_invariants();

    let node = tree.get(&1).expect("item not found");
    unsafe { tree.remove(node.get_ref().into()) };
    tree.assert_invariants();

    let node = tree.get(&3).expect("item not found");
    unsafe { tree.remove(node.get_ref().into()) };
    tree.assert_invariants();

    drop(tree);
}

use std::ptr::NonNull;

use cordyceps::Linked;
use cordyceps_wavl::{Links, WavlTree};

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

fn main() {
    let mut tree: WavlTree<TestNode, u32> = WavlTree::new();

    tree.insert(Box::new(TestNode {
        links: Links::new(0_u32),
    }));

    tree.insert(Box::new(TestNode {
        links: Links::new(2_u32),
    }));

    tree.insert(Box::new(TestNode {
        links: Links::new(3_u32),
    }));

    tree.insert(Box::new(TestNode {
        links: Links::new(1_u32),
    }));

    drop(tree);
}

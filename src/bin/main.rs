use std::{
    fs::File,
    io::Write,
    path::{Path, PathBuf},
    ptr::NonNull,
};

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

struct MultiGraph {
    id: u32,
    dir: PathBuf,
}

impl MultiGraph {
    fn new(dir: impl AsRef<Path>) -> MultiGraph {
        let dir = dir.as_ref();
        std::fs::create_dir_all(dir).unwrap();

        MultiGraph {
            id: 0,
            dir: dir.to_owned(),
        }
    }

    fn emit_dotgraph(&mut self, tree: &WavlTree<TestNode>) {
        let mut s = String::new();
        tree.dotgraph::<_, &u32>(&self.id.to_string(), &mut s)
            .unwrap();

        let mut f = File::options()
            .create_new(true)
            .write(true)
            .open(self.dir.join(format!("graph-{:03}.dot", self.id)))
            .unwrap();

        f.write_all(s.as_bytes()).unwrap();

        self.id += 1;
    }
}

fn main() {
    let mut tree: WavlTree<TestNode> = WavlTree::new();

    let mut mg = MultiGraph::new("graphs");

    for value in [611, 0, 612, 551, 552, 1, 2, 3, 4, 553, 17, 18, 19, 5] {
        tree.insert(TestNode::new(value));
        tree.assert_invariants();
        //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());
    }

    assert_eq!(tree.first().unwrap().key, 0);
    tree.insert(TestNode::new(0));
    tree.assert_invariants();

    assert_eq!(tree.pop_last().unwrap().key, 612);
    tree.assert_invariants();
    //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    tree.insert(TestNode::new(20));
    tree.assert_invariants();
    //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    assert_eq!(tree.first().unwrap().key, 0);
    tree.insert(TestNode::new(0));
    tree.assert_invariants();

    for value in [611, 553, 552] {
        assert_eq!(tree.pop_last().unwrap().key, value);
        mg.emit_dotgraph(&tree);
        tree.assert_invariants();
        //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());
    }

    assert_eq!(tree.last().unwrap().key, 551);

    let seventeen = tree.remove(&17);
    assert!(seventeen.is_some());
    mg.emit_dotgraph(&tree);
    tree.assert_invariants();
    //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    assert_eq!(tree.pop_last().unwrap().key, 551);
    mg.emit_dotgraph(&tree);
    tree.assert_invariants();
    //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    assert_eq!(tree.pop_last().unwrap().key, 20);
    mg.emit_dotgraph(&tree);
    tree.assert_invariants();
    //println!("{:?}", tree.iter().map(|node| node.key).collect::<Vec<_>>());

    drop(tree);
}

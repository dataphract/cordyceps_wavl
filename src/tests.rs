extern crate std;

use std::{ops::Range, prelude::v1::*};

use proptest::prelude::*;

use crate::model::{self, TestNode};

use super::*;

fn insert_find_all(keys: &[u32]) {
    let mut tree: WavlTree<TestNode> = WavlTree::new();

    for &key in keys {
        tree.insert(Box::new(TestNode {
            links: Links::new(),
            key,
        }));
        tree.assert_invariants();
    }

    for key in keys {
        let node = tree.get_raw(key).expect("item not found");
        assert_eq!(unsafe { node.as_ref().key() }, key);
    }
}

#[test]
fn zero_elems_find() {
    insert_find_all(&[]);
}

#[test]
fn single_elem_find() {
    insert_find_all(&[0]);
}

#[test]
fn two_elems_find() {
    insert_find_all(&[0, 1]);
    insert_find_all(&[1, 0]);
}

#[test]
fn three_elems_find() {
    insert_find_all(&[0, 1, 2]);
    insert_find_all(&[0, 2, 1]);
    insert_find_all(&[1, 0, 2]);
    insert_find_all(&[1, 2, 0]);
    insert_find_all(&[2, 0, 1]);
    insert_find_all(&[2, 1, 0]);
}

#[test]
fn four_elems_find() {
    insert_find_all(&[0, 1, 2, 3]);
    insert_find_all(&[0, 1, 3, 2]);
    insert_find_all(&[0, 2, 1, 3]);
    insert_find_all(&[0, 2, 3, 1]);
    insert_find_all(&[0, 3, 1, 2]);
    insert_find_all(&[0, 3, 2, 1]);

    insert_find_all(&[1, 0, 2, 3]);
    insert_find_all(&[1, 0, 3, 2]);
    insert_find_all(&[1, 2, 0, 3]);
    insert_find_all(&[1, 2, 3, 0]);
    insert_find_all(&[1, 3, 0, 2]);
    insert_find_all(&[1, 3, 2, 0]);

    insert_find_all(&[2, 0, 1, 3]);
    insert_find_all(&[2, 0, 3, 1]);
    insert_find_all(&[2, 1, 0, 3]);
    insert_find_all(&[2, 1, 3, 0]);
    insert_find_all(&[2, 3, 0, 1]);
    insert_find_all(&[2, 3, 1, 0]);

    insert_find_all(&[3, 0, 1, 2]);
    insert_find_all(&[3, 0, 2, 1]);
    insert_find_all(&[3, 1, 0, 2]);
    insert_find_all(&[3, 1, 2, 0]);
    insert_find_all(&[3, 2, 0, 1]);
    insert_find_all(&[3, 2, 1, 0]);
}

fn insert_remove_all(keys: &[u32]) {
    let mut tree: WavlTree<TestNode> = WavlTree::new();

    for &key in keys {
        tree.insert(Box::new(TestNode {
            links: Links::new(),
            key,
        }));
        tree.assert_invariants();
    }

    for key in keys {
        let node = tree.get_raw(key).expect("item not found");
        unsafe { tree.remove_at(node) };
        tree.assert_invariants();
    }

    for &key in keys {
        tree.insert(Box::new(TestNode {
            links: Links::new(),
            key,
        }));
        tree.assert_invariants();
    }

    for key in keys.iter().rev() {
        let node = tree.get_raw(key).expect("item not found");
        unsafe { tree.remove_at(node) };
        tree.assert_invariants();
    }
}

#[test]
fn remove_one() {
    insert_remove_all(&[0]);
}

#[test]
fn remove_two() {
    insert_remove_all(&[0, 1]);
    insert_remove_all(&[1, 0]);
}

#[test]
fn remove_three() {
    insert_remove_all(&[0, 1, 2]);
    insert_remove_all(&[0, 2, 1]);
    insert_remove_all(&[1, 0, 2]);
    insert_remove_all(&[1, 2, 0]);
    insert_remove_all(&[2, 0, 1]);
    insert_remove_all(&[2, 1, 0]);
}

#[test]
fn remove_four() {
    insert_remove_all(&[0, 1, 2, 3]);
    insert_remove_all(&[0, 1, 3, 2]);
    insert_remove_all(&[0, 2, 1, 3]);
    insert_remove_all(&[0, 2, 3, 1]);
    insert_remove_all(&[0, 3, 1, 2]);
    insert_remove_all(&[0, 3, 2, 1]);

    insert_remove_all(&[1, 0, 2, 3]);
    insert_remove_all(&[1, 0, 3, 2]);
    insert_remove_all(&[1, 2, 0, 3]);
    insert_remove_all(&[1, 2, 3, 0]);
    insert_remove_all(&[1, 3, 0, 2]);
    insert_remove_all(&[1, 3, 2, 0]);

    insert_remove_all(&[2, 0, 1, 3]);
    insert_remove_all(&[2, 0, 3, 1]);
    insert_remove_all(&[2, 1, 0, 3]);
    insert_remove_all(&[2, 1, 3, 0]);
    insert_remove_all(&[2, 3, 0, 1]);
    insert_remove_all(&[2, 3, 1, 0]);

    insert_remove_all(&[3, 0, 1, 2]);
    insert_remove_all(&[3, 0, 2, 1]);
    insert_remove_all(&[3, 1, 0, 2]);
    insert_remove_all(&[3, 1, 2, 0]);
    insert_remove_all(&[3, 2, 0, 1]);
    insert_remove_all(&[3, 2, 1, 0]);
}

#[test]
fn test_predecessor_successor() {
    let mut wavl: WavlTree<TestNode> = WavlTree::new();

    for i in 0..10 {
        wavl.insert(TestNode::new(i));
    }

    for (i, elem) in wavl.iter().enumerate() {
        let pred = if i > 0 {
            wavl.iter().nth(i - 1).map(NonNull::from)
        } else {
            None
        };

        let succ = wavl.iter().nth(i + 1).map(NonNull::from);

        assert_eq!(
            pred,
            unsafe { wavl.predecessor_raw(elem.into()) },
            "key = {i}"
        );
        assert_eq!(
            succ,
            unsafe { wavl.successor_raw(elem.into()) },
            "key = {i}"
        );
    }
}

#[test]
fn test_first() {
    let mut wavl: WavlTree<TestNode> = WavlTree::new();

    // Ensure replacement updates first, last.
    wavl.insert(TestNode::new(1));
    let old = wavl.insert(TestNode::new(1)).unwrap();
    assert_ne!(wavl.first().map(NonNull::from), Some(NonNull::from(&*old)));

    wavl.clear();

    wavl.insert(TestNode::new(3));
    wavl.insert(TestNode::new(2));
    wavl.insert(TestNode::new(1));

    assert_eq!(wavl.first().unwrap().key, 1);
}

#[test]
fn test_cursor_wraps_around() {
    let mut tree: WavlTree<TestNode> = WavlTree::new();
    tree.insert(TestNode::new(0));
    tree.insert(TestNode::new(1));

    let mut curs = tree.cursor_first();
    assert_eq!(curs.get().map(TestNode::key), Some(&0));

    curs.move_prev();
    assert_eq!(curs.get().map(TestNode::key), None);

    curs.move_prev();
    assert_eq!(curs.get().map(TestNode::key), Some(&1));

    curs.move_next();
    assert_eq!(curs.get().map(TestNode::key), None);

    curs.move_next();
    assert_eq!(curs.get().map(TestNode::key), Some(&0));
}

#[cfg(miri)]
const FUZZ_RANGE: Range<usize> = 0..10;

#[cfg(not(miri))]
const FUZZ_RANGE: Range<usize> = 0..1000;

proptest::proptest! {
    #![proptest_config(ProptestConfig {
        max_shrink_iters: 65536,
        .. ProptestConfig::default()
    })]

    #[test]
    fn btree_equivalence(ops in proptest::collection::vec(model::op_strategy(), FUZZ_RANGE)) {
        model::run_btree_equivalence(ops);
    }
}

proptest::proptest! {
    #![proptest_config(ProptestConfig {
        max_shrink_iters: 65536,
        .. ProptestConfig::default()
    })]

    #[test]
    fn cursor_equivalence(
        values in proptest::collection::vec(proptest::bits::u32::ANY, 100),
        ops in proptest::collection::vec(model::cursor_op_strategy(), FUZZ_RANGE),
    ) {
        model::run_cursor_equivalence(values, ops)
    }
}

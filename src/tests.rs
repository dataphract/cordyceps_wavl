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

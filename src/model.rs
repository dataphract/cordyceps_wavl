extern crate std;

use std::{collections::BTreeSet, prelude::v1::*, ptr::NonNull};

use arbitrary::Arbitrary;
use cordyceps::Linked;
use proptest::strategy::{Just, Strategy};

use crate::{Links, TreeNode, WavlTree};

#[derive(Debug)]
#[repr(C)]
pub struct TestNode {
    pub links: Links<TestNode>,
    pub key: u32,
}

impl TestNode {
    pub(crate) fn new(key: u32) -> Box<TestNode> {
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

#[derive(Copy, Clone, Debug, Arbitrary)]
pub enum ItemValue {
    Index(usize),
    Random(u32),
}

proptest::prop_compose! {
    fn index_strategy()(
        index in 0usize..1000,
    ) -> ItemValue {
        ItemValue::Index(index)
    }
}

proptest::prop_compose! {
    fn random_strategy()(
        random in 0u32..1000,
    ) -> ItemValue {
        ItemValue::Random(random)
    }
}

fn value_strategy() -> impl Strategy<Value = ItemValue> {
    proptest::prop_oneof![index_strategy(), random_strategy()]
}

#[derive(Copy, Clone, Debug, Arbitrary)]
pub enum Op {
    Insert(ItemValue),
    // TryInsert(ItemValue),
    Get(ItemValue),
    Remove(ItemValue),
    First,
    PopFirst,
    Last,
    PopLast,
}

impl Op {
    fn finalize(self, sorted: &[u32]) -> FinalOp {
        fn get_value(v: &[u32], i: ItemValue) -> u32 {
            match i {
                ItemValue::Index(idx) => {
                    if v.is_empty() {
                        idx as u32
                    } else {
                        v[idx % v.len().max(1)]
                    }
                }
                ItemValue::Random(v) => v,
            }
        }

        match self {
            Op::Insert(item) => FinalOp::Insert(get_value(sorted, item)),
            Op::Get(item) => FinalOp::Get(get_value(sorted, item)),
            Op::Remove(item) => FinalOp::Remove(get_value(sorted, item)),
            Op::First => FinalOp::First,
            Op::PopFirst => FinalOp::PopFirst,
            Op::Last => FinalOp::Last,
            Op::PopLast => FinalOp::PopLast,
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum FinalOp {
    Insert(u32),
    Get(u32),
    Remove(u32),
    First,
    PopFirst,
    Last,
    PopLast,
}

pub fn op_strategy() -> impl Strategy<Value = Op> {
    proptest::prop_oneof![
        value_strategy().prop_map(Op::Insert),
        value_strategy().prop_map(Op::Get),
        value_strategy().prop_map(Op::Remove),
        Just(Op::First),
        Just(Op::PopFirst),
        Just(Op::Last),
        Just(Op::PopLast),
    ]
}

pub fn run_btree_equivalence(ops: Vec<Op>) {
    let mut sorted_values = Vec::with_capacity(ops.len());
    let mut btree = BTreeSet::new();
    let mut wavl: WavlTree<TestNode> = WavlTree::new();

    fn insert_sorted(v: &mut Vec<u32>, value: u32) {
        if let Err(idx) = v.binary_search(&value) {
            v.insert(idx, value);
        }
    }

    fn remove_sorted(v: &mut Vec<u32>, value: u32) {
        if let Ok(idx) = v.binary_search(&value) {
            v.remove(idx);
        }
    }

    #[inline]
    #[allow(clippy::boxed_local)]
    fn node_key(node: Box<TestNode>) -> u32 {
        node.key
    }

    #[inline]
    fn ref_key(node: &TestNode) -> &u32 {
        &node.key
    }

    let mut final_ops = Vec::with_capacity(ops.len());
    for (op_id, op) in ops.into_iter().enumerate() {
        let final_op = op.finalize(&sorted_values);
        final_ops.push(final_op);

        match final_op {
            FinalOp::Insert(value) => {
                insert_sorted(&mut sorted_values, value);

                let from_btree = if btree.insert(value) {
                    None
                } else {
                    Some(value)
                };
                let from_wavl = wavl.insert(TestNode::new(value)).map(node_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }

            // FinalOp::TryInsert(_) => todo!(),
            FinalOp::Get(value) => {
                let from_btree = btree.get(&value);
                let from_wavl = wavl.get(&value).map(ref_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }

            FinalOp::Remove(value) => {
                remove_sorted(&mut sorted_values, value);

                let from_btree = btree.remove(&value).then_some(value);
                let from_wavl = wavl.remove(&value).map(node_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }

            FinalOp::First => {
                let from_btree = btree.first();
                let from_wavl = wavl.first().map(ref_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }

            FinalOp::PopFirst => {
                let from_btree = btree.pop_first();
                let from_wavl = wavl.pop_first().map(node_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }

            FinalOp::Last => {
                let from_btree = btree.first();
                let from_wavl = wavl.first().map(ref_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }

            FinalOp::PopLast => {
                let from_btree = btree.pop_last();
                let from_wavl = wavl.pop_last().map(node_key);

                assert_eq!(from_btree, from_wavl, "FinalOp #{op_id}: {op:?}");
            }
        }

        wavl.assert_invariants();
        assert_eq!(btree.len(), wavl.len());
        assert!(btree.iter().zip(wavl.iter()).all(|(&a, b)| a == b.key));
    }
}

#[derive(Clone, Debug, Arbitrary)]
pub enum CursorOp {
    // Get is not an operation as it's executed on every loop iteration to check equivalence.
    MovePrev,
    MoveNext,
    PeekNext,
    PeekPrev,
    RemoveCurrent,
    RemoveCurrentMovePrev,
}

pub fn cursor_op_strategy() -> impl Strategy<Value = CursorOp> {
    proptest::prop_oneof![
        Just(CursorOp::MovePrev),
        Just(CursorOp::MoveNext),
        Just(CursorOp::PeekNext),
        Just(CursorOp::PeekPrev),
        Just(CursorOp::RemoveCurrent),
        Just(CursorOp::RemoveCurrentMovePrev),
    ]
}

#[derive(Clone, Debug)]
pub struct CursorEquivalenceInput {
    pub values: Vec<u32>,
    pub ops: Vec<CursorOp>,
}

impl<'a> arbitrary::Arbitrary<'a> for CursorEquivalenceInput {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        fn value(u: &mut arbitrary::Unstructured<'_>) -> u32 {
            u32::arbitrary(u).unwrap_or(0)
        }

        fn op(u: &mut arbitrary::Unstructured<'_>) -> CursorOp {
            CursorOp::arbitrary(u).unwrap_or(CursorOp::MoveNext)
        }

        let num_values = u8::arbitrary(u)? % 100;
        let num_ops = u16::arbitrary(u)? % 1000;

        let values = core::iter::repeat_with(|| value(u))
            .take(num_values.into())
            .collect();

        let ops = core::iter::repeat_with(|| op(u))
            .take(num_ops.into())
            .collect();

        Ok(CursorEquivalenceInput { values, ops })
    }
}

pub fn run_cursor_equivalence(mut values: Vec<u32>, ops: Vec<CursorOp>) {
    values.sort_unstable();
    values.dedup();

    // Ideally this would be a BTreeMap cursor or even a LinkedList cursor, but neither is stable :(
    let mut vec = Vec::new();
    let mut wavl: WavlTree<TestNode> = WavlTree::new();

    for val in values {
        vec.push(val);
        wavl.insert(TestNode::new(val));
    }

    fn vec_curs_prev(v: &Vec<u32>, curs: Option<usize>) -> Option<usize> {
        match curs {
            Some(i) => i.checked_sub(1),
            None => v.len().checked_sub(1),
        }
    }

    fn vec_curs_next(v: &Vec<u32>, curs: Option<usize>) -> Option<usize> {
        match curs {
            Some(i) => i.checked_add(1).filter(|&i| i < v.len()),
            None => (!v.is_empty()).then_some(0),
        }
    }

    let mut vec_curs = vec_curs_next(&vec, None);
    let mut wavl_curs = wavl.cursor_first_mut();

    // Check that the initial states are equivalent.
    {
        let v = vec_curs.map(|i| &vec[i]);
        let w = wavl_curs.get().map(TestNode::key);

        assert_eq!(v, w);
    }

    for op in ops {
        match op {
            CursorOp::MoveNext => {
                vec_curs = vec_curs_next(&vec, vec_curs);
                wavl_curs.move_next();
            }

            CursorOp::MovePrev => {
                vec_curs = vec_curs_prev(&vec, vec_curs);
                wavl_curs.move_prev();
            }

            CursorOp::PeekNext => {
                let v = vec_curs_next(&vec, vec_curs).map(|i| &vec[i]);
                let w = wavl_curs.peek_next().map(TestNode::key);

                assert_eq!(v, w);
            }

            CursorOp::PeekPrev => {
                let v = vec_curs_prev(&vec, vec_curs).map(|i| &vec[i]);
                let w = wavl_curs.peek_prev().map(TestNode::key);

                assert_eq!(v, w);
            }

            CursorOp::RemoveCurrent => {
                let v = vec_curs.map(|i| vec.remove(i));

                if vec_curs == Some(vec.len()) {
                    vec_curs = None;
                }

                let w = wavl_curs.remove_current().map(|node| node.key);

                assert_eq!(v, w);
            }

            CursorOp::RemoveCurrentMovePrev => {
                let new_v_curs = vec_curs.is_some().then(|| vec_curs_prev(&vec, vec_curs));
                let v = vec_curs.map(|i| vec.remove(i));

                if let Some(vc) = new_v_curs {
                    vec_curs = vc;
                }

                let w = wavl_curs
                    .remove_current_and_move_prev()
                    .map(|node| node.key);

                assert_eq!(v, w);
            }
        }

        let v = vec_curs.map(|i| &vec[i]);
        let w = wavl_curs.get().map(TestNode::key);

        assert_eq!(v, w);
    }
}

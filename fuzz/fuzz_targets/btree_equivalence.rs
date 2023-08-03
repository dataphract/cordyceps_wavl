#![no_main]
use libfuzzer_sys::{
    arbitrary::{Arbitrary, Unstructured},
    fuzz_target,
};

use cordyceps_wavl::model::{run_btree_equivalence, Op};

fuzz_target!(|ops: Vec<Op>| { run_btree_equivalence(ops) });

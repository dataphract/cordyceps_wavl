#![no_main]

use cordyceps_wavl::model::CursorEquivalenceInput;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|input: CursorEquivalenceInput| {
    cordyceps_wavl::model::run_cursor_equivalence(input.values, input.ops);
});

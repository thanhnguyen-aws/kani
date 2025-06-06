// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Check if harness work loop contracts macro can be proved correctly
//! without loop contracts enable.

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

pub const BASE: usize = count_zero(&[]);

#[kani::proof]
pub fn check_counter() {
    assert_eq!(count_zero(&[1, 2, 3]), 0)
}

const fn count_zero(slice: &[u8]) -> usize {
    let mut counter: usize = 0;
    let mut index: usize = 0;

    #[kani::loop_invariant(index <= slice.len() && counter <= slice.len() && counter == 0 )]
    while index < slice.len() {
        if slice[index] == 0 {
            counter += 1;
        }
        index += 1;
    }

    counter
}

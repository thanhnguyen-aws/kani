// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Checks that `round_ties_even_f64` returns the nearest integer to the argument. The
// default rounding mode is rounding half to even, which is described here:
// https://en.wikipedia.org/wiki/Rounding#Round_half_to_even
#![feature(core_intrinsics)]
use std::intrinsics::round_ties_even_f64;

#[kani::proof]
fn test_one() {
    let one = 1.0;
    let result = round_ties_even_f64(one);
    assert!(result == 1.0);
}

#[kani::proof]
fn test_one_frac() {
    let one_frac = 1.9;
    let result = round_ties_even_f64(one_frac);
    assert!(result == 2.0);
}

#[kani::proof]
fn test_half_down() {
    let one_frac = 2.5;
    let result = round_ties_even_f64(one_frac);
    assert!(result == 2.0);
}

#[kani::proof]
fn test_half_up() {
    let one_frac = 3.5;
    let result = round_ties_even_f64(one_frac);
    assert!(result == 4.0);
}

#[kani::proof]
fn test_conc() {
    let conc = -42.6;
    let result = round_ties_even_f64(conc);
    assert!(result == -43.0);
}

#[kani::proof]
fn test_conc_sci() {
    let conc = 5.4e-2;
    let result = round_ties_even_f64(conc);
    assert!(result == 0.0);
}

#[kani::proof]
fn test_towards_nearest() {
    let x: f64 = kani::any();
    kani::assume(!x.is_nan());
    kani::assume(!x.is_infinite());
    let result = round_ties_even_f64(x);
    let frac = x.fract().abs();
    if x.is_sign_positive() {
        if frac > 0.5 {
            assert!(result > x);
        } else if frac < 0.5 {
            assert!(result <= x);
        } else {
            // This would fail if conversion checks were on
            let integer = x as i64;
            if integer % 2 == 0 {
                assert!(result < x);
            } else {
                assert!(result > x);
            }
        }
    } else {
        if frac > 0.5 {
            assert!(result < x);
        } else if frac < 0.5 {
            assert!(result >= x);
        } else {
            // This would fail if conversion checks were on
            let integer = x as i64;
            if integer % 2 == 0 {
                assert!(result > x);
            } else {
                assert!(result < x);
            }
        }
    }
}

#[kani::proof]
fn test_diff_half_one() {
    let x: f64 = kani::any();
    kani::assume(!x.is_nan());
    kani::assume(!x.is_infinite());
    let result = round_ties_even_f64(x);
    let diff = (x - result).abs();
    assert!(diff <= 0.5);
    assert!(diff >= 0.0);
}

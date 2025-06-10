// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This macro generates implementations of the `KaniIntoIter` trait for various common types that are used in for loop.
//! We use this trait to overwrite the Rust IntoIter trait to reduce call stacks and avoid complicated loop invariant specifications,
//! while maintaining the semantic of the loop.

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! generate_iter {
    () => {
        use core_path::iter::Chain;
        use core_path::mem as stdmem;
        use core_path::slice::Iter;

        pub trait KaniIter
        where
            Self: Sized,
        {
            type Item;
            fn indexing(&self, i: usize) -> Self::Item;
            fn first(&self) -> Self::Item;
            fn assumption(&self);
        }

        pub struct KaniSingleIter<T: Copy> {
            pub ptr: *const T,
            pub len: usize,
        }

        impl<T: Copy> KaniSingleIter<T> {
            pub fn new(ptr: *const T, len: usize) -> Self {
                KaniSingleIter { ptr, len }
            }
        }

        impl<T: Copy> KaniIter for KaniSingleIter<T> {
            type Item = T;
            fn indexing(&self, i: usize) -> Self::Item {
                unsafe { *self.ptr.wrapping_add(i) }
            }
            fn first(&self) -> Self::Item {
                unsafe { *self.ptr }
            }
            fn assumption(&self) {
                kani::assume(unsafe {
                    self.len == 0 || kani::mem::is_allocated(self.ptr as *const (), self.len)
                });
            }
        }

        pub trait KaniIntoIter
        where
            Self: Sized,
        {
            type Iter: KaniIter;
            fn kani_into_iter(self) -> Self::Iter;
        }

        impl<T: Copy, const N: usize> KaniIntoIter for [T; N] {
            type Iter = KaniSingleIter<T>;
            fn kani_into_iter(self) -> Self::Iter {
                KaniSingleIter::new(self.as_ptr(), N)
            }
        }

        impl<T: Copy> KaniIntoIter for Iter<'_, T> {
            type Iter = KaniSingleIter<T>;
            fn kani_into_iter(self) -> Self::Iter {
                KaniSingleIter::new(self.as_slice().as_ptr(), self.len())
            }
        }

        impl<'a, T: Copy> KaniIntoIter for &'a [T] {
            type Iter = KaniSingleIter<T>;
            fn kani_into_iter(self) -> Self::Iter {
                KaniSingleIter::new(self.as_ptr(), self.len())
            }
        }

        impl<'a, T: Copy> KaniIntoIter for &'a mut [T] {
            type Iter = KaniSingleIter<T>;
            fn kani_into_iter(self) -> Self::Iter {
                KaniSingleIter::new(self.as_ptr(), self.len())
            }
        }

        impl<T: Copy> KaniIntoIter for Vec<T> {
            type Iter = KaniSingleIter<T>;
            fn kani_into_iter(self) -> Self::Iter {
                let s = self.iter();
                KaniSingleIter::new(s.as_slice().as_ptr(), s.len())
            }
        }
    };
}

use std::sync::atomic::{AtomicPtr, Ordering};

use backend::*;

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

pub fn transposed_par_for_each_mut<A, V, const N: usize, G>(array: &mut [V; N], g: G)
where
    A: Send + Sync,
    V: std::ops::DerefMut<Target = [A]>,
    G: Fn(usize, [&mut A; N]) + Sync,
{
    // all vectors must have the same length
    let len = array[0].len();
    let data_ptrs: [AtomicPtr<A>; N] = array.each_mut().map(|v| AtomicPtr::new(v.as_mut_ptr()));

    parallel::for_each_index(len, |i| {
        let row: [&mut A; N] = unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].load(Ordering::Relaxed).add(i)) };
        g(i, row);
    });
}

#[derive(Debug, Clone, Default)]
pub struct Counter(usize);

impl Counter {
    pub fn get_next(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }

    pub fn new() -> Self {
        Self(0)
    }
}

pub fn decode_hex(s: &str) -> Vec<u8> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

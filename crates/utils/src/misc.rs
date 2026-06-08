use backend::*;

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

pub fn transposed_par_for_each_mut<A: Send + Sync, const N: usize>(
    array: &mut [ArenaVec<A>; N], // all vectors must have the same length
    f: impl Fn(usize, [&mut A; N]) + Sync,
) {
    let len = array[0].len();
    let data_ptrs: [parallel::SendPtr<A>; N] = std::array::from_fn(|j| parallel::SendPtr(array[j].as_mut_ptr()));
    parallel::for_each_index(len, |i| {
        // SAFETY: distinct `i` index disjoint rows across all N columns; the column base pointers
        // stay valid for the whole call (`array` is borrowed mutably for its duration).
        let row: [&mut A; N] = unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].0.add(i)) };
        f(i, row);
    });
}

pub fn collect_refs<T>(vecs: &[Vec<T>]) -> Vec<&[T]> {
    vecs.iter().map(Vec::as_slice).collect()
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

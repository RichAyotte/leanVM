use crate::{
    DIMENSION, EF, EXT_OP_FLAG_ADD, EXT_OP_FLAG_IS_BE, EXT_OP_FLAG_MUL, EXT_OP_FLAG_POLY_EQ, ExtraDataForBuses,
    eval_bus_virtual,
    tables::extension_op::{EXT_OP_LEN_MULTIPLIER, ExtensionOpPrecompile},
};
use backend::*;

// ---------- Column layout (cubic extension, DIMENSION = 3) ----------
// Shift columns first, in positions 0..11 (see `n_shift_columns` below).
// Flat-only columns follow.
pub(super) const COL_IS_BE: usize = 0;
pub(super) const COL_START: usize = 1;
pub(super) const COL_LEN: usize = 2;
pub(super) const COL_FLAG_ADD: usize = 3;
pub(super) const COL_FLAG_MUL: usize = 4;
pub(super) const COL_FLAG_POLY_EQ: usize = 5;
pub(super) const COL_IDX_A: usize = 6;
pub(super) const COL_IDX_B: usize = 7;
/// computation coordinates (3 cols).
pub(super) const COL_COMP: usize = 8;
// --- flat-only columns ---
pub(super) const COL_IDX_RES: usize = 11;
/// value_a coordinates (3 cols).
pub(super) const COL_VA: usize = 12;
/// value_b coordinates (3 cols).
pub(super) const COL_VB: usize = 15;
/// result coordinates (3 cols).
pub(super) const COL_VRES: usize = 18;

// Virtual columns (not explicitely in AIR)
pub(super) const COL_MULTIPLICITY_EXTENSION_OP: usize = 21;
pub(super) const COL_DOMAINSEP_EXTENSION_OP: usize = 22;

pub(super) const AIR_N_COLUMNS: usize = 21;

// ---------- Cubic multiplication gate (`F[X] / (X^3 - X - 1)`, so `X^3 = X + 1`) ----------
//
// (a0 + a1·X + a2·X^2)·(b0 + b1·X + b2·X^2), reduced:
//   c0 = a0·b0 + a1·b2 + a2·b1
//   c1 = a0·b1 + a1·b0 + a1·b2 + a2·b1 + a2·b2
//   c2 = a0·b2 + a1·b1 + a2·b0 + a2·b2
#[inline]
fn cubic_mul_air<T: PrimeCharacteristicRing + Copy>(a: &[T; 3], b: &[T; 3]) -> [T; 3] {
    let a1b2 = a[1] * b[2];
    let a2b1 = a[2] * b[1];
    let a2b2 = a[2] * b[2];
    [
        a[0] * b[0] + a1b2 + a2b1,
        a[0] * b[1] + a[1] * b[0] + a1b2 + a2b1 + a2b2,
        a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + a2b2,
    ]
}

impl<const BUS: bool> Air for ExtensionOpPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        AIR_N_COLUMNS
    }
    fn degree_air(&self) -> usize {
        // cubic_mul has degree 2 (elementwise), wrapped in `* flag_mul` gives 3; poly_eq
        // squares that via another cubic_mul so needs degree 4? In the KoalaBear case the
        // eval used `6` — we retain a conservative upper bound.
        6
    }
    fn n_constraints(&self) -> usize {
        // 5 boolean gates
        // + 3 * flag_add
        // + 3 * flag_mul
        // + 3 * flag_poly_eq
        // + 3 * start (vres vs comp)
        // + 6 transition gates (len/is_be/flags/idx transitions) + 1 start-row-length
        // + 1 bus (if BUS)
        5 + 3 + 3 + 3 + 3 + 7 + BUS as usize
    }
    fn n_shift_columns(&self) -> usize {
        COL_COMP + 3
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let flat = builder.flat();
        let shift = builder.shift();

        let is_be = flat[COL_IS_BE];
        let start = flat[COL_START];
        let flag_add = flat[COL_FLAG_ADD];
        let flag_mul = flat[COL_FLAG_MUL];
        let flag_poly_eq = flat[COL_FLAG_POLY_EQ];
        let len = flat[COL_LEN];
        let idx_a = flat[COL_IDX_A];
        let idx_b = flat[COL_IDX_B];

        let va: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_VA + k]);
        let vb: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_VB + k]);
        let vres: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_VRES + k]);
        let comp: [AB::IF; 3] = std::array::from_fn(|k| flat[COL_COMP + k]);

        // Shift columns map 1:1 onto the first 11 columns by convention.
        let is_be_shift = shift[COL_IS_BE];
        let start_shift = shift[COL_START];
        let len_shift = shift[COL_LEN];
        let flag_add_shift = shift[COL_FLAG_ADD];
        let flag_mul_shift = shift[COL_FLAG_MUL];
        let flag_poly_eq_shift = shift[COL_FLAG_POLY_EQ];
        let idx_a_shift = shift[COL_IDX_A];
        let idx_b_shift = shift[COL_IDX_B];
        let comp_shift: [AB::IF; 3] = std::array::from_fn(|k| shift[COL_COMP + k]);

        let active = flag_add + flag_mul + flag_poly_eq;
        let multiplicity = start * active;

        let aux = is_be * AB::F::from_usize(EXT_OP_FLAG_IS_BE)
            + flag_add * AB::F::from_usize(EXT_OP_FLAG_ADD)
            + flag_mul * AB::F::from_usize(EXT_OP_FLAG_MUL)
            + flag_poly_eq * AB::F::from_usize(EXT_OP_FLAG_POLY_EQ)
            + len * AB::F::from_usize(EXT_OP_LEN_MULTIPLIER);

        let idx_r = flat[COL_IDX_RES];

        if BUS {
            eval_bus_virtual::<AB, EF>(builder, extra_data, multiplicity, aux, &[idx_a, idx_b, idx_r]);
        } else {
            builder.declare_values(&[multiplicity]);
            builder.declare_values(&[idx_a, idx_b, idx_r, aux]);
        }

        let is_ee = -(is_be - AB::F::ONE);
        let not_start_shift = -(start_shift - AB::F::ONE);

        // For "base-extension" ops, value_a is a base-field scalar embedded into EF as
        // `(va[0], 0, 0)`: zero the upper coordinates when `is_be` is 1.
        let va_f_or_ef: [AB::IF; 3] = std::array::from_fn(|k| if k == 0 { va[0] } else { va[k] * is_ee });

        let comp_tail: [AB::IF; 3] = std::array::from_fn(|k| comp_shift[k] * not_start_shift);

        builder.assert_bool(is_be);
        builder.assert_bool(start);
        builder.assert_bool(flag_add);
        builder.assert_bool(flag_mul);
        builder.assert_bool(flag_poly_eq);

        for k in 0..3 {
            builder.assert_zero((comp[k] - (va_f_or_ef[k] + vb[k] + comp_tail[k])) * flag_add);
        }

        let va_times_vb = cubic_mul_air(&va_f_or_ef, &vb);

        for k in 0..3 {
            builder.assert_zero((comp[k] - (va_times_vb[k] + comp_tail[k])) * flag_mul);
        }

        // poly_eq per element: `2 a b - a - b + 1` (constant coord only gets +1),
        // accumulated via multiplication.
        let poly_eq_val: [AB::IF; 3] = std::array::from_fn(|k| {
            let base = va_times_vb[k].double() - va_f_or_ef[k] - vb[k];
            if k == 0 { base + AB::F::ONE } else { base }
        });
        let comp_shift_or_one: [AB::IF; 3] = std::array::from_fn(|k| {
            if k == 0 {
                comp_shift[0] * not_start_shift + start_shift
            } else {
                comp_shift[k] * not_start_shift
            }
        });
        let poly_eq_result = cubic_mul_air(&poly_eq_val, &comp_shift_or_one);
        for k in 0..3 {
            builder.assert_zero((comp[k] - poly_eq_result[k]) * flag_poly_eq);
        }

        for k in 0..3 {
            builder.assert_zero((comp[k] - vres[k]) * start);
        }

        builder.assert_zero(not_start_shift * (len - len_shift - AB::F::ONE));
        builder.assert_zero(not_start_shift * (is_be - is_be_shift));
        builder.assert_zero(not_start_shift * (flag_add - flag_add_shift));
        builder.assert_zero(not_start_shift * (flag_mul - flag_mul_shift));
        builder.assert_zero(not_start_shift * (flag_poly_eq - flag_poly_eq_shift));
        let a_increment = is_be + is_ee * AB::F::from_usize(DIMENSION);
        builder.assert_zero(not_start_shift * (idx_a_shift - idx_a - a_increment));
        builder.assert_zero(not_start_shift * (idx_b_shift - idx_b - AB::F::from_usize(DIMENSION)));

        builder.assert_zero(start_shift * (len - AB::F::ONE));
    }
}

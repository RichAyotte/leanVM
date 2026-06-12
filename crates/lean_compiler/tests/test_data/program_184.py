from snark_lib import *

"""
Exercises ALL 7 poseidon8 precompile variants and cross-checks them against
each other, so that a regression in the compiler's variant -> flag lowering
(permute / half_output / hardcoded_offset_left, cf. a_simplify_lang) breaks
this program. It also guarantees every variant appears in the test_data corpus
for differential bytecode comparisons.

Semantics (snark_lib.py, "Poseidon8 precompiles"); P = raw Poseidon permutation:
  input = left(4 cells) || right(4 cells)
  permute family:  output = P(input)           (8 cells; low 4 for `_half`)
  compress family: output = P(input) + input   (low 4 cells; low 2 for `_quarter`)
  `_hardcoded_left(L, R, O, off)`: left = m[off..off+2] || m[L..L+2]
Cells past a variant's output length are NOT written; this is checked below by
writing sentinels afterwards (the write-once rule would reject a conflict).

Limitation (verified by mutation testing): a variant writing FEWER cells than
expected is NOT caught at execution, because the VM's memory solver back-fills
unwritten cells from the asserts (the mechanism powering range checks). The
guard for that direction is differential bytecode comparison across compiler
changes -- which this program enables by putting all 7 variants in test_data.
"""

HARD_PTR = 4  # 2 preamble cells, right after the 4-cell public input region


def main():
    # Known, pairwise-distinct values at the compile-time address HARD_PTR,
    # so a corrupted `off` would change the hardcoded-left results below.
    hard = HARD_PTR
    hard[0] = 101
    hard[1] = 102

    left = Array(4)
    right = Array(4)
    for i in unroll(0, 4):
        left[i] = 10 + i
        right[i] = 20 + i

    # The effective left input of the hardcoded-left variants, materialized.
    left_hard = Array(4)
    for i in unroll(0, 2):
        left_hard[i] = hard[i]
        left_hard[i + 2] = left[i]

    # permute vs permute_half: same low 4 cells; permute_half writes ONLY 4.
    out_p = Array(8)
    out_ph = Array(8)
    poseidon8_permute(left, right, out_p)
    poseidon8_permute_half(left, right, out_ph)
    for i in unroll(0, 4):
        assert out_ph[i] == out_p[i]
    for i in unroll(4, 8):
        out_ph[i] = 0  # would conflict if permute_half had written 8 cells

    # compress_half = permutation + feed-forward of the left half.
    out_ch = Array(4)
    poseidon8_compress_half(left, right, out_ch)
    for i in unroll(0, 4):
        assert out_ch[i] == out_p[i] + left[i]

    # compress_quarter: same low 2 cells as compress_half, writes ONLY 2.
    out_cq = Array(4)
    poseidon8_compress_quarter(left, right, out_cq)
    for i in unroll(0, 2):
        assert out_cq[i] == out_ch[i]
        out_cq[i + 2] = 0  # would conflict if compress_quarter had written 4 cells

    # hardcoded-left variants == plain variants applied to `left_hard`.
    out_chl = Array(4)
    out_ch2 = Array(4)
    poseidon8_compress_half_hardcoded_left(left, right, out_chl, HARD_PTR)
    poseidon8_compress_half(left_hard, right, out_ch2)
    for i in unroll(0, 4):
        assert out_chl[i] == out_ch2[i]

    out_cql = Array(4)
    poseidon8_compress_quarter_hardcoded_left(left, right, out_cql, HARD_PTR)
    for i in unroll(0, 2):
        assert out_cql[i] == out_ch2[i]
        out_cql[i + 2] = 0  # would conflict on a 4-cell write

    out_phl = Array(4)
    out_ph2 = Array(4)
    poseidon8_permute_half_hardcoded_left(left, right, out_phl, HARD_PTR)
    poseidon8_permute_half(left_hard, right, out_ph2)
    for i in unroll(0, 4):
        assert out_phl[i] == out_ph2[i]

    return

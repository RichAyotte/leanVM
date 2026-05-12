from recursion import *
from xmss_aggregate import *

MAX_RECURSIONS = 16

# TODO increase (we would need a bigger minimal memory size, totally doable)
MAX_N_SIGS = 2**15
MAX_N_DUPS = 2**15

INNER_PUB_MEM_SIZE = 2**INNER_PUBLIC_MEMORY_LOG_SIZE  # = DIGEST_LEN

INPUT_DATA_SIZE_PADDED = INPUT_DATA_SIZE_PADDED_PLACEHOLDER
INPUT_DATA_NUM_CHUNKS = INPUT_DATA_SIZE_PADDED / DIGEST_LEN
# Layout: n_sigs (1) | pairs_hash (DIGEST_LEN) | bytecode_claim | bytecode_hash_domsep.
# The per-signer message rides into the VM via the `pairs` hint, not the
# public input, so the claim starts right after the pairs hash.
BYTECODE_CLAIM_OFFSET = 1 + DIGEST_LEN
BYTECODE_HASH_DOMSEP_OFFSET = BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED
BYTECODE_SUMCHECK_PROOF_SIZE = BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER

# Per-pair stride in the `all_pairs` buffer: 8 (pubkey) + 9 (message) + 7 (zero
# pad) = 24 FE, rounded to a multiple of DIGEST_LEN so the hash helpers stay
# chunk-aligned. The pad keeps the buffer addressable with constant stride; it
# must agree with `PAIR_STRIDE_FE` in `rec_aggregation/src/lib.rs`.
PAIR_STRIDE = 3 * DIGEST_LEN
N_CHUNKS_PER_PAIR = PAIR_STRIDE / DIGEST_LEN


def main():
    debug_assert(MAX_N_SIGS + MAX_N_DUPS <= 2**16)  # because of range checking, TODO increase
    pub_mem = 0 # See hashing.py for the memory layout
    build_preamble_memory()

    data_buf = Array(INPUT_DATA_SIZE_PADDED)
    hint_witness("input_data", data_buf)
    n_sigs = data_buf[0]
    assert n_sigs != 0
    assert n_sigs - 1 < MAX_N_SIGS
    pairs_hash_expected = data_buf + 1
    bytecode_claim_output = data_buf + BYTECODE_CLAIM_OFFSET
    bytecode_hash_domsep = data_buf + BYTECODE_HASH_DOMSEP_OFFSET

    # meta = [n_recursions, n_dup, pairs_len, n_raw_xmss]
    meta = Array(4)
    hint_witness("meta", meta)
    n_recursions = meta[0]
    assert n_recursions <= MAX_RECURSIONS

    n_dup = meta[1]
    assert n_dup < MAX_N_SIGS  # TODO increase

    all_pairs = Array(meta[2])
    hint_witness("pairs", all_pairs)
    n_raw_xmss = meta[3]
    raw_indices = Array(n_raw_xmss)
    hint_witness("raw_indices", raw_indices)

    aggregate_sizes = Array(n_recursions)
    hint_witness("aggregate_sizes", aggregate_sizes)

    # 1->1 optimization
    if n_recursions == 1:
        assert n_dup == 0
        if n_raw_xmss == 0:
            inner_data_buf = build_inner_data_buf(
                n_sigs, pairs_hash_expected, bytecode_hash_domsep,
            )

            inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
            copy_8(slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS), inner_pub_mem)
            bytecode_claims = Array(2)
            bytecode_claims[0] = inner_data_buf + BYTECODE_CLAIM_OFFSET
            bytecode_claims[1] = recursion(inner_pub_mem, bytecode_hash_domsep)
            reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output)
            # All fields of `data_buf` are now written: hash it and assert the digest
            # matches the (single-element) public input by writing into public memory.
            outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
            copy_8(outer_hash, pub_mem)
            return

    # General path
    computed_pairs_hash = slice_hash_with_iv_dynamic_unroll(all_pairs, n_sigs * PAIR_STRIDE, MAX_LOG_MEMORY_SIZE)
    copy_8(computed_pairs_hash, pairs_hash_expected)

    # Buffer for partition verification
    n_total = n_sigs + n_dup
    buffer = Array(n_total)

    for i in parallel_range(0, n_raw_xmss):
        # mark buffer for partition verification
        idx = raw_indices[i]
        assert idx < n_total
        buffer[idx] = i
        # Each signer carries its own slot (read from the signature hint) and
        # its own message (read from the `pairs` blob at this index). The
        # pair layout is `pk (DIGEST_LEN) | msg (MESSAGE_LEN) | zero pad`.
        pair = all_pairs + idx * PAIR_STRIDE
        pk = pair
        msg = pair + DIGEST_LEN
        xmss_verify(pk, msg)

    counter: Mut = n_raw_xmss

    # Recursive sources
    n_bytecode_claims = n_recursions * 2
    bytecode_claims = Array(n_bytecode_claims)

    for rec_idx in range(0, n_recursions):
        sub_indices_blob = Array(aggregate_sizes[rec_idx])
        hint_witness("sub_indices", sub_indices_blob)
        n_sub = sub_indices_blob[0]
        assert n_sub != 0
        assert n_sub < MAX_N_SIGS
        sub_indices_arr = sub_indices_blob + 1

        # Chain-compress the child's pair list to reproduce the same digest
        # the child's VM checks internally via slice_hash_with_iv. Each pair
        # contributes N_CHUNKS_PER_PAIR poseidon compresses; the first chunk
        # of the first pair uses ZERO_VEC_PTR as the IV.
        idx0 = sub_indices_arr[0]
        assert idx0 < n_total
        buffer[idx0] = counter
        counter += 1
        pair0 = all_pairs + idx0 * PAIR_STRIDE
        running_hash: Mut = Array(DIGEST_LEN)
        poseidon16_compress(ZERO_VEC_PTR, pair0, running_hash)
        for k in unroll(1, N_CHUNKS_PER_PAIR):
            chunk = pair0 + k * DIGEST_LEN
            new_hash = Array(DIGEST_LEN)
            poseidon16_compress(running_hash, chunk, new_hash)
            running_hash = new_hash

        for j in dynamic_unroll(1, n_sub, log2_ceil(MAX_N_SIGS)):
            idx = sub_indices_arr[j]
            assert idx < n_total
            buffer[idx] = counter
            counter += 1
            pair = all_pairs + idx * PAIR_STRIDE
            for k in unroll(0, N_CHUNKS_PER_PAIR):
                chunk = pair + k * DIGEST_LEN
                new_hash = Array(DIGEST_LEN)
                poseidon16_compress(running_hash, chunk, new_hash)
                running_hash = new_hash

        inner_data_buf = build_inner_data_buf(
            n_sub, running_hash, bytecode_hash_domsep,
        )
        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        copy_8(slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS), inner_pub_mem)

        bytecode_claims[2 * rec_idx] = inner_data_buf + BYTECODE_CLAIM_OFFSET
        # Verify recursive proof - returns the second bytecode claim
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, bytecode_hash_domsep)

    # Ensure partition validity
    assert counter == n_total

    # Bytecode claims
    if n_recursions == 0:
        for k in unroll(0, BYTECODE_POINT_N_VARS):
            set_to_5_zeros(bytecode_claim_output + k * DIM)
        bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM] = BYTECODE_ZERO_EVAL
        for k in unroll(1, DIM):
            bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM + k] = 0
    else:
        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output)

    # All fields of `data_buf` are now written: hash it and assert the digest
    # matches the (single-element) public input by writing into public memory.
    outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
    copy_8(outer_hash, pub_mem)
    return

def reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output):
    bytecode_claims_hash: Mut = ZERO_VEC_PTR
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        claim_hash = slice_hash(claim_ptr, BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN)
        new_hash = Array(DIGEST_LEN)
        poseidon16_compress(bytecode_claims_hash, claim_hash, new_hash)
        bytecode_claims_hash = new_hash

    bytecode_sumcheck_proof = Array(BYTECODE_SUMCHECK_PROOF_SIZE)
    hint_witness("bytecode_sumcheck_proof", bytecode_sumcheck_proof)
    reduction_fs: Mut = fs_new(bytecode_sumcheck_proof)
    reduction_fs, received_claims_hash = fs_receive_chunks(reduction_fs, 1)
    copy_8(bytecode_claims_hash, received_claims_hash)

    reduction_fs, alpha = fs_sample_ef(reduction_fs)
    alpha_powers = powers(alpha, n_bytecode_claims)

    all_values = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        copy_5(claim_ptr + BYTECODE_POINT_N_VARS * DIM, all_values + i * DIM)

    claimed_sum = Array(DIM)
    dot_product_ee_dynamic(all_values, alpha_powers, claimed_sum, n_bytecode_claims)

    reduction_fs, challenges, final_eval = sumcheck_verify(reduction_fs, BYTECODE_POINT_N_VARS, claimed_sum, 2)

    # Verify: final_eval == bytecode(r) * w(r)
    eq_evals = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        poly_eq_ee(claim_ptr, challenges, eq_evals + i * DIM, BYTECODE_POINT_N_VARS)
    w_r = Array(DIM)
    dot_product_ee_dynamic(eq_evals, alpha_powers, w_r, n_bytecode_claims)

    bytecode_value_at_r = div_extension_ret(final_eval, w_r)

    copy_many_ef(challenges, bytecode_claim_output, BYTECODE_POINT_N_VARS)
    copy_5(bytecode_value_at_r, bytecode_claim_output + BYTECODE_POINT_N_VARS * DIM)
    return

@inline
def build_inner_data_buf(n_sub, pairs_hash, bytecode_hash_domsep):
    inner_data_buf = Array(INPUT_DATA_SIZE_PADDED)
    inner_data_buf[0] = n_sub
    copy_8(pairs_hash, inner_data_buf + 1)
    hint_witness("inner_bytecode_claim", inner_data_buf + BYTECODE_CLAIM_OFFSET)
    copy_8(bytecode_hash_domsep, inner_data_buf + BYTECODE_HASH_DOMSEP_OFFSET)
    for k in unroll(BYTECODE_HASH_DOMSEP_OFFSET + DIGEST_LEN, INPUT_DATA_SIZE_PADDED):
        inner_data_buf[k] = 0
    return inner_data_buf

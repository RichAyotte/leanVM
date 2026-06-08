use backend::*;

pub use backend::ProofError;
pub use leansig_wrapper::{
    MESSAGE_LENGTH, XmssPublicKey, XmssSignature, xmss_keygen_fast, xmss_sign_fast, xmss_verify,
};
pub use rec_aggregation::{
    AggregatedXMSS, AggregatedXMSSInfo, AggregationError, AggregationTopology, MAX_RECURSIONS, MAX_XMSS_AGGREGATED,
    MAX_XMSS_DUPLICATES, ProverError, xmss_aggregate, xmss_verify_aggregation,
};

pub type F = KoalaBear;

/// Call once before proving. Enables the proving arena, compiles the aggregation program, and
/// precomputes DFT twiddles.
///
/// # Safety
/// Never generate two proofs concurrently in one process. (The arena allocator has a single shared
/// region per process, so concurrent proving corrupts each proof's buffers.) Use separate processes
/// to parallelize.
pub fn setup_prover() {
    zk_alloc::enable_arena();
    parallel::init();
    rec_aggregation::init_aggregation_bytecode();
    precompute_dft_twiddles::<F>(1 << 24);
}

/// Call once before verifying (not needed if `setup_prover` was already called).
pub fn setup_verifier() {
    rec_aggregation::init_aggregation_bytecode();
}

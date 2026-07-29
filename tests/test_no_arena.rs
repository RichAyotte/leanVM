use lean_multisig::{aggregate_single_message_signatures, setup_prover_without_arena, verify_single_message_aggregate};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

#[test]
fn aggregate_without_arena() {
    setup_prover_without_arena();
    let signatures = get_benchmark_signatures()[0..2].to_vec();
    let aggregated =
        aggregate_single_message_signatures(&[], signatures, message_for_benchmark(), BENCHMARK_SLOT, 2).unwrap();
    verify_single_message_aggregate(&aggregated).unwrap();
}

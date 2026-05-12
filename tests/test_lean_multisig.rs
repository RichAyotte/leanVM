use backend::{KoalaBear, PrimeCharacteristicRing};
use lean_multisig::{AggregatedXMSS, AggregationTopology, setup_prover, xmss_aggregate, xmss_verify_aggregation};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::run_aggregation_benchmark;
use xmss::{
    signers_cache::{get_benchmark_signatures, message_for_benchmark},
    xmss_key_gen, xmss_sign, xmss_verify,
};

#[test]
fn test_xmss_signature() {
    let start_slot = 111;
    let end_slot = 200;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let msg = rng.random();

    let (secret_key, pub_key) = xmss_key_gen(rng.random(), start_slot, end_slot).unwrap();
    let signature = xmss_sign(&mut rng, &secret_key, &msg, slot).unwrap();
    xmss_verify(&pub_key, &msg, &signature).unwrap();
}

#[test]
fn test_aggregation() {
    for n_signatures in [1, 2, 4, 8, 16, 32, 64, 128] {
        let topology = AggregationTopology {
            raw_xmss: n_signatures,
            children: vec![],
            log_inv_rate: 1,
        };
        run_aggregation_benchmark(&topology, 0, false);
    }
}

/// Minimal aggregation test that does not depend on
/// `signers_cache::get_benchmark_signatures` (which precomputes 10k
/// signers and dominates wall-clock time on a fresh checkout). Builds
/// two XMSS signers on different slots in line, then aggregates and
/// verifies. Exercises the per-signer-slot path end to end: each
/// `XmssSignature` carries its own slot, the prover packs `slot_lo`,
/// `slot_hi`, and the Merkle nibbles into the per-signature hint blob,
/// and the VM reads them back to verify the Merkle path.
#[test]
fn test_aggregation_inline_distinct_slots() {
    setup_prover();
    let log_inv_rate = 2;

    let message: [KoalaBear; xmss::MESSAGE_LEN_FE] =
        std::array::from_fn(|i| KoalaBear::from_usize(i + 1));

    let mk = |seed_u64: u64, slot: u32| {
        let mut rng = StdRng::seed_from_u64(seed_u64);
        let (sk, pk) = xmss_key_gen(rng.random(), slot, slot).unwrap();
        let sig = xmss_sign(&mut rng, &sk, &message, slot).unwrap();
        (pk, sig)
    };

    let raw = vec![mk(1, 5), mk(2, 13)];
    let (pub_keys, agg) = xmss_aggregate(&[], raw, &message, log_inv_rate);

    xmss_verify_aggregation(&pub_keys, &agg, &message).unwrap();
}

#[test]
fn test_recursive_aggregation() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let signatures = get_benchmark_signatures();

    let pub_keys_and_sigs_a = signatures[0..3].to_vec();
    let (pub_keys_a, aggregated_a) = xmss_aggregate(&[], pub_keys_and_sigs_a, &message, log_inv_rate);

    let pub_keys_and_sigs_b = signatures[3..5].to_vec();
    let (pub_keys_b, aggregated_b) = xmss_aggregate(&[], pub_keys_and_sigs_b, &message, log_inv_rate);

    let pub_keys_and_sigs_c = signatures[5..6].to_vec();

    let children: Vec<(&[_], AggregatedXMSS)> = vec![(&pub_keys_a, aggregated_a), (&pub_keys_b, aggregated_b)];
    let (final_pub_keys, aggregated_final) =
        xmss_aggregate(&children, pub_keys_and_sigs_c, &message, log_inv_rate);

    let serialized_final = aggregated_final.serialize();
    println!("Serialized aggregated final: {} KiB", serialized_final.len() / 1024);
    let deserialized_final = AggregatedXMSS::deserialize(&serialized_final).unwrap();

    xmss_verify_aggregation(&final_pub_keys, &deserialized_final, &message).unwrap();
}

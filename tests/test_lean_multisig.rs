use backend::{KoalaBear, PrimeCharacteristicRing};
use lean_multisig::{AggregatedXMSS, AggregationTopology, setup_prover, xmss_aggregate, xmss_verify_aggregation};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::run_aggregation_benchmark;
use xmss::{
    MESSAGE_LEN_FE, XmssPublicKey, XmssSignature,
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
/// two XMSS signers signing *different* messages at different slots in
/// line, then aggregates and verifies. Exercises the per-signer slot
/// path AND the per-signer message path end to end: each `XmssSignature`
/// carries its own slot; the prover packs each signer's message into
/// the global pairs buffer; and the VM reads `(pk_i, msg_i)` per
/// iteration to verify the signature.
#[test]
fn test_aggregation_inline_distinct_pairs() {
    setup_prover();
    let log_inv_rate = 2;

    let mk = |seed_u64: u64, slot: u32, msg_seed: usize| {
        let mut rng = StdRng::seed_from_u64(seed_u64);
        let (sk, pk) = xmss_key_gen(rng.random(), slot, slot).unwrap();
        let message: [KoalaBear; xmss::MESSAGE_LEN_FE] = std::array::from_fn(|i| KoalaBear::from_usize(i + msg_seed));
        let sig = xmss_sign(&mut rng, &sk, &message, slot).unwrap();
        (pk, message, sig)
    };

    let raw = vec![mk(1, 5, 100), mk(2, 13, 200)];
    let expected_pairs: Vec<_> = {
        let mut v: Vec<_> = raw.iter().map(|(pk, msg, _)| (pk.clone(), *msg)).collect();
        v.sort();
        v
    };
    let (pairs, agg) = xmss_aggregate(&[], raw, log_inv_rate);
    assert_eq!(pairs, expected_pairs);

    xmss_verify_aggregation(&pairs, &agg).unwrap();
}

#[test]
fn test_recursive_aggregation() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let signatures = get_benchmark_signatures();

    // Benchmark signatures all share the same message; tag each entry with it
    // to feed the per-signer-message API.
    let with_msg =
        |slice: &[(XmssPublicKey, XmssSignature)]| -> Vec<(XmssPublicKey, [KoalaBear; MESSAGE_LEN_FE], XmssSignature)> {
            slice
                .iter()
                .map(|(pk, sig)| (pk.clone(), message, sig.clone()))
                .collect()
        };

    let raw_a = with_msg(&signatures[0..3]);
    let (pairs_a, aggregated_a) = xmss_aggregate(&[], raw_a, log_inv_rate);

    let raw_b = with_msg(&signatures[3..5]);
    let (pairs_b, aggregated_b) = xmss_aggregate(&[], raw_b, log_inv_rate);

    let raw_c = with_msg(&signatures[5..6]);

    let children: Vec<(&[_], AggregatedXMSS)> = vec![(&pairs_a, aggregated_a), (&pairs_b, aggregated_b)];
    let (final_pairs, aggregated_final) = xmss_aggregate(&children, raw_c, log_inv_rate);

    let serialized_final = aggregated_final.serialize();
    println!("Serialized aggregated final: {} KiB", serialized_final.len() / 1024);
    let deserialized_final = AggregatedXMSS::deserialize(&serialized_final).unwrap();

    xmss_verify_aggregation(&final_pairs, &deserialized_final).unwrap();
}

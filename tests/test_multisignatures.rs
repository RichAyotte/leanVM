use std::sync::{Mutex, MutexGuard};
use std::time::Instant;

use lean_multisig::{
    MultiMessageAggregateSignature, SingleMessageAggregateSignature, aggregate_single_message_signatures,
    merge_single_message_aggregates, setup_prover, split_multi_message_aggregate, verify_multi_message_aggregate,
    verify_single_message_aggregate,
};
use leansig_wrapper::{xmss_keygen_fast, xmss_sign_fast, xmss_verify};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::{AggregationTopology, run_aggregation_benchmark};
use rec_aggregation::signatures_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};
use rec_aggregation::split_multi_message_aggregate_by_message;

static ARENA_TEST_LOCK: Mutex<()> = Mutex::new(());

fn serialize_arena_tests() -> MutexGuard<'static, ()> {
    ARENA_TEST_LOCK.lock().unwrap()
}

#[test]
fn test_xmss_signature() {
    let activation_epoch = 111;
    let num_active_epochs = 39;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let message = [42u8; leansig_wrapper::MESSAGE_LENGTH];

    let (secret_key, pub_key) = xmss_keygen_fast(&mut rng, activation_epoch, num_active_epochs);
    let signature = xmss_sign_fast(&secret_key, &message, slot).unwrap();
    xmss_verify(&pub_key, slot, &message, &signature).unwrap();
}

#[test]
fn test_aggregation() {
    let _arena_guard = serialize_arena_tests();
    for n_signatures in [1, 2, 4, 8, 16, 32, 64, 128] {
        let topology = AggregationTopology {
            raw_xmss: n_signatures,
            children: vec![],
            log_inv_rate: 1,
            overlap: 0,
        };
        run_aggregation_benchmark(&topology, false, true, 1);
    }
}

#[test]
fn test_single_message_aggregation() {
    let _arena_guard = serialize_arena_tests();
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let single_message_a = aggregate_single_message_signatures(&[], raws_a, message, slot, log_inv_rate).unwrap();

    let raws_b = signatures[3..5].to_vec();
    let single_message_b = aggregate_single_message_signatures(&[], raws_b, message, slot, log_inv_rate).unwrap();

    let raws_c = signatures[5..6].to_vec();
    let final_sig = aggregate_single_message_signatures(
        &[single_message_a, single_message_b],
        raws_c,
        message,
        slot,
        log_inv_rate,
    )
    .unwrap();

    let serialized_proof = final_sig.compress();
    println!("Serialized aggregated final: {} KiB", serialized_proof.len() / 1024);
    let recovered = SingleMessageAggregateSignature::decompress(&serialized_proof).unwrap();

    verify_single_message_aggregate(&recovered).unwrap();
}

#[test]
fn test_multi_message_aggregation() {
    let _arena_guard = serialize_arena_tests();
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let slot_a = BENCHMARK_SLOT;
    let message_a = message_for_benchmark();
    let signatures = get_benchmark_signatures();
    let raws_a = signatures[0..3].to_vec();

    let slot_b = BENCHMARK_SLOT + 1;
    let mut rng_b: StdRng = StdRng::seed_from_u64(17);
    let message_b: [u8; leansig_wrapper::MESSAGE_LENGTH] = std::array::from_fn(|_| rng_b.random());

    assert!(message_b != message_a && slot_b != slot_a);

    let raws_b: Vec<_> = (0..2)
        .map(|_| {
            let (sk, pk) = xmss_keygen_fast(&mut rng_b, slot_b, 1);
            let sig = xmss_sign_fast(&sk, &message_b, slot_b).unwrap();
            (pk, sig)
        })
        .collect();

    let single_message_a = aggregate_single_message_signatures(&[], raws_a, message_a, slot_a, log_inv_rate).unwrap();
    let single_message_b = aggregate_single_message_signatures(&[], raws_b, message_b, slot_b, log_inv_rate).unwrap();

    verify_single_message_aggregate(&single_message_a).unwrap();
    verify_single_message_aggregate(&single_message_b).unwrap();

    let info_a = single_message_a.info.clone();
    let info_b = single_message_b.info.clone();

    let time = Instant::now();
    let multi_message =
        merge_single_message_aggregates(vec![single_message_a, single_message_b], log_inv_rate).unwrap();
    println!("merge_single_message_aggregates: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(multi_message.info.len(), 2);
    assert_eq!(multi_message.info[0], info_a);
    assert_eq!(multi_message.info[1], info_b);

    verify_multi_message_aggregate(&multi_message).unwrap();

    let time = Instant::now();
    let split_a = split_multi_message_aggregate(multi_message.clone(), 0, log_inv_rate).unwrap();
    println!("split index 0: {:.2}s", time.elapsed().as_secs_f64());
    let time = Instant::now();
    let split_b = split_multi_message_aggregate_by_message(multi_message, message_b, log_inv_rate).unwrap();
    println!("split index 1: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(
        (
            split_a.info.without_pubkeys.message,
            &split_a.info.without_pubkeys.slot,
            &split_a.info.pubkeys,
        ),
        (
            info_a.without_pubkeys.message,
            &info_a.without_pubkeys.slot,
            &info_a.pubkeys,
        )
    );
    assert_eq!(
        (
            split_b.info.without_pubkeys.message,
            &split_b.info.without_pubkeys.slot,
            &split_b.info.pubkeys,
        ),
        (
            info_b.without_pubkeys.message,
            &info_b.without_pubkeys.slot,
            &info_b.pubkeys,
        )
    );
    verify_single_message_aggregate(&split_a).expect("split index 0 failed verify_single_message_aggregate");
    verify_single_message_aggregate(&split_b).expect("split index 1 failed verify_single_message_aggregate");
}

#[test]
fn test_single_multi_message_compression() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    // The pubkey set is shared between prover and verifier.
    let raws_a = signatures[..3].to_vec();
    let shared_pubkeys_a = raws_a.iter().map(|(pk, _)| pk.clone()).collect::<Vec<_>>();
    let single_message_a = aggregate_single_message_signatures(&[], raws_a, message, slot, log_inv_rate).unwrap();

    let single_message_a_compressed_compact = single_message_a.compress_without_pubkeys();
    let single_message_a_compact_recovered = SingleMessageAggregateSignature::decompress_without_pubkeys(
        &single_message_a_compressed_compact,
        shared_pubkeys_a,
    )
    .expect("single-message round-trip");
    verify_single_message_aggregate(&single_message_a_compact_recovered).expect("recovered single-message must verify");
    assert_eq!(
        single_message_a_compact_recovered.info.pubkeys,
        single_message_a.info.pubkeys
    );

    let single_message_a_compressed_full = single_message_a.compress();
    let single_message_a_full_recovered =
        SingleMessageAggregateSignature::decompress(&single_message_a_compressed_full)
            .expect("single-message round-trip");
    verify_single_message_aggregate(&single_message_a_full_recovered).expect("recovered single-message must verify");
    assert_eq!(
        single_message_a_full_recovered.info.pubkeys,
        single_message_a.info.pubkeys
    );

    assert!(single_message_a_compressed_compact.len() < single_message_a_compressed_full.len());

    let slot_b = BENCHMARK_SLOT + 1;
    let mut rng_b: StdRng = StdRng::seed_from_u64(17);
    let message_b: [u8; leansig_wrapper::MESSAGE_LENGTH] = std::array::from_fn(|_| rng_b.random());
    let raws_b: Vec<_> = (0..2)
        .map(|_| {
            let (sk, pk) = xmss_keygen_fast(&mut rng_b, slot_b, 1);
            let xs = xmss_sign_fast(&sk, &message_b, slot_b).unwrap();
            (pk, xs)
        })
        .collect();
    let single_message_b = aggregate_single_message_signatures(&[], raws_b, message_b, slot_b, log_inv_rate).unwrap();

    let multi_message =
        merge_single_message_aggregates(vec![single_message_a, single_message_b], log_inv_rate).unwrap();
    let shared_pubkeys_multi_message: Vec<_> = multi_message.info.iter().map(|i| i.pubkeys.clone()).collect();

    let multi_message_compressed_compact = multi_message.compress_without_pubkeys();
    let multi_message_compact_recovered = MultiMessageAggregateSignature::decompress_without_pubkeys(
        &multi_message_compressed_compact,
        shared_pubkeys_multi_message,
    )
    .expect("multi-message round-trip");
    verify_multi_message_aggregate(&multi_message_compact_recovered).expect("recovered multi-message must verify");
    assert_eq!(multi_message_compact_recovered.info, multi_message.info);

    let multi_message_compressed_full = multi_message.compress();
    let multi_message_full_recovered =
        MultiMessageAggregateSignature::decompress(&multi_message_compressed_full).expect("multi-message round-trip");
    verify_multi_message_aggregate(&multi_message_full_recovered).expect("recovered multi-message must verify");
    assert_eq!(multi_message_full_recovered.info, multi_message.info);

    assert!(multi_message_compressed_compact.len() < multi_message_compressed_full.len());
}

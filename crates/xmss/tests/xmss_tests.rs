use backend::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use xmss::*;

type F = KoalaBear;

#[test]
fn test_xmss_serialize_deserialize() {
    let keygen_seed: [u8; 20] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));
    let slot_start = 100;
    let slot_end = 115;
    let slot = 110;

    let (sk, pk) = xmss_key_gen(keygen_seed, slot_start, slot_end).unwrap();
    let sig = xmss_sign(&mut StdRng::seed_from_u64(slot as u64), &sk, &message, slot).unwrap();

    let pk_bytes = postcard::to_allocvec(&pk).unwrap();
    let pk2: XmssPublicKey = postcard::from_bytes(&pk_bytes).unwrap();
    assert_eq!(pk, pk2);

    let sig_bytes = postcard::to_allocvec(&sig).unwrap();
    let sig2: XmssSignature = postcard::from_bytes(&sig_bytes).unwrap();
    assert_eq!(sig, sig2);

    xmss_verify(&pk2, &message, &sig2).unwrap();
}

#[test]
fn keygen_sign_verify() {
    let keygen_seed: [u8; 20] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));

    let slot_start = 100;
    let slot_end = 115;
    let (sk, pk) = xmss_key_gen(keygen_seed, slot_start, slot_end).unwrap();
    for slot in slot_start..=slot_end {
        let sig = xmss_sign(&mut StdRng::seed_from_u64(u64::from(slot)), &sk, &message, slot).unwrap();
        xmss_verify(&pk, &message, &sig).unwrap();
    }
}

#[test]
fn a_restored_secret_key_signs_as_the_original() {
    let keygen_seed: [u8; 20] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));
    let (sk, pk) = xmss_key_gen(keygen_seed, 100, 115).unwrap();

    let restored: XmssSecretKey = postcard::from_bytes(&postcard::to_allocvec(&sk).unwrap()).unwrap();

    assert_eq!(restored.public_key(), pk);
    assert_eq!(restored.slot_range(), 100..=115);
    for slot in 100..=115 {
        let rng = || StdRng::seed_from_u64(u64::from(slot));
        let original = xmss_sign(&mut rng(), &sk, &message, slot).unwrap();
        let from_restored = xmss_sign(&mut rng(), &restored, &message, slot).unwrap();
        assert_eq!(from_restored, original, "slot {slot}");
    }
    assert_eq!(
        xmss_sign(&mut StdRng::seed_from_u64(0), &restored, &message, 116),
        Err(XmssSignatureError::SlotOutOfRange),
        "the restored key lost its range"
    );
}

/// The try a seeded search accepts at, and the chain indices it yields. Every
/// try before the accepted one was refused, so a change to either the digest or
/// the acceptance rule moves one of the two.
#[test]
fn the_encoding_a_seeded_search_finds_is_pinned() {
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));
    let root: [F; TRUNCATED_MERKLE_ROOT_LEN_FE] = std::array::from_fn(|i| F::from_usize(i + 1000));
    let (_, encoding, tries) =
        find_randomness_for_wots_encoding(&message, 0x0001_0203, &root, &mut StdRng::seed_from_u64(1));
    assert_eq!(
        (tries, encoding),
        (
            37458,
            [
                4, 7, 2, 5, 5, 4, 5, 5, 6, 2, 0, 6, 4, 3, 7, 4, 4, 5, 1, 6, 6, 7, 2, 7, 3, 4, 6, 5, 4, 7, 5, 2, 1, 5,
                6, 4, 2, 6, 7, 5, 1, 4
            ]
        )
    );
}

/// Randomness is transposed into the packing and digests out of it, so a lane
/// read from the wrong position answers for another lane's randomness.
#[test]
fn packed_encoding_agrees_with_wots_encode() {
    type Packed = <F as Field>::Packing;
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));
    let root: [F; TRUNCATED_MERKLE_ROOT_LEN_FE] = std::array::from_fn(|i| F::from_usize(i + 1000));
    // Both 16-bit halves nonzero, so neither half's place in the digest goes
    // unchecked
    let slot = 0x0001_0203;
    let mut rng = StdRng::seed_from_u64(1);

    let mut accepted = 0;
    while accepted < 3 {
        let lanes: [[F; RANDOMNESS_LEN_FE]; Packed::WIDTH] = std::array::from_fn(|_| rng.random());
        let packed = wots_encode_packed(&message, slot, &root, &lanes);
        for (lane, randomness) in lanes.iter().enumerate() {
            let scalar = wots_encode(&message, slot, &root, randomness);
            assert_eq!(packed[lane], scalar, "lane {lane}");
            accepted += usize::from(scalar.is_some());
        }
    }
}

#[test]
#[ignore]
fn encoding_grinding_bits() {
    let n = 100;
    let total_iters = (0..n)
        .into_par_iter()
        .map(|i| {
            let message: [F; MESSAGE_LEN_FE] = Default::default();
            let slot = i as u32;
            let truncated_merkle_root: [F; TRUNCATED_MERKLE_ROOT_LEN_FE] = Default::default();
            let mut rng = StdRng::seed_from_u64(i as u64);
            let (_randomness, _encoding, num_iters) =
                find_randomness_for_wots_encoding(&message, slot, &truncated_merkle_root, &mut rng);
            num_iters
        })
        .sum::<usize>();
    let grinding = ((total_iters as f64) / (n as f64)).log2();
    println!("Average grinding bits: {:.1}", grinding);
}

// SPDX-FileCopyrightText: 2026 Nomadic Labs <contact@nomadic-labs.com>

use backend::{KoalaBear as F, PrimeCharacteristicRing, PrimeField32};
use octez_rust_lean_multisig_encoding::{
    DecodeError, KOALA_BEAR_PRIME, MESSAGE_BYTES_LEN, MESSAGE_LEN_FE, PUBLIC_KEY_BYTES_LEN,
    PUBLIC_KEY_LEN_FE, SIGNATURE_BYTES_LEN, SIGNATURE_LEN_FE, compose_limbs, decompose_bytes,
    decompose_bytes_canonical, divmod_by_p_in_place, message_to_field_elements,
    public_key_from_bytes, public_key_to_bytes, signature_from_bytes, signature_to_bytes,
};
use xmss::{LOG_LIFETIME, RANDOMNESS_LEN_FE, V, WotsSignature, XmssPublicKey, XmssSignature};

fn from_le_u256(words: [u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, w) in words.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
    }
    out
}

// ---------------------------------------------------------------------------
// Math layer (decompose_bytes / compose_limbs / divmod_by_p_in_place):
// known-vector tests against the base-`P` decomposition.
// ---------------------------------------------------------------------------

#[test]
fn decompose_zero_message_buffer() {
    let limbs = decompose_bytes(&[0u8; MESSAGE_BYTES_LEN], MESSAGE_LEN_FE);
    assert_eq!(limbs, vec![0u32; MESSAGE_LEN_FE]);
}

#[test]
fn decompose_one_message_buffer() {
    let mut bytes = [0u8; MESSAGE_BYTES_LEN];
    bytes[0] = 1;
    let limbs = decompose_bytes(&bytes, MESSAGE_LEN_FE);
    assert_eq!(limbs[0], 1);
    assert!(limbs[1..].iter().all(|&l| l == 0));
}

#[test]
fn decompose_p_message_buffer() {
    let bytes = from_le_u256([u64::from(KOALA_BEAR_PRIME), 0, 0, 0]);
    let limbs = decompose_bytes(&bytes, MESSAGE_LEN_FE);
    assert_eq!(limbs[0], 0);
    assert_eq!(limbs[1], 1);
    assert!(limbs[2..].iter().all(|&l| l == 0));
}

#[test]
fn decompose_p_plus_one_message_buffer() {
    let bytes = from_le_u256([u64::from(KOALA_BEAR_PRIME) + 1, 0, 0, 0]);
    let limbs = decompose_bytes(&bytes, MESSAGE_LEN_FE);
    assert_eq!(limbs[0], 1);
    assert_eq!(limbs[1], 1);
    assert!(limbs[2..].iter().all(|&l| l == 0));
}

#[test]
fn decompose_p_squared_message_buffer() {
    let p = u128::from(KOALA_BEAR_PRIME);
    let p_squared = p * p;
    let lo = p_squared as u64;
    let hi = (p_squared >> 64) as u64;
    let bytes = from_le_u256([lo, hi, 0, 0]);
    let limbs = decompose_bytes(&bytes, MESSAGE_LEN_FE);
    assert_eq!(limbs[0], 0);
    assert_eq!(limbs[1], 0);
    assert_eq!(limbs[2], 1);
    assert!(limbs[3..].iter().all(|&l| l == 0));
}

#[test]
fn decompose_canonical_range() {
    let bytes: [u8; MESSAGE_BYTES_LEN] =
        std::array::from_fn(|i| (i as u8).wrapping_mul(13).wrapping_add(7));
    let limbs = decompose_bytes(&bytes, MESSAGE_LEN_FE);
    for &limb in &limbs {
        assert!(limb < KOALA_BEAR_PRIME, "non-canonical limb: {limb:#x}");
    }
}

#[test]
fn decompose_matches_independent_reference() {
    // Independently re-implement int_to_base_p over a u256 represented as
    // 8 little-endian u32 words; check decompose_bytes matches.
    let bytes: [u8; MESSAGE_BYTES_LEN] =
        std::array::from_fn(|i| (i as u8).wrapping_mul(17).wrapping_add(3));
    let limbs = decompose_bytes(&bytes, MESSAGE_LEN_FE);

    let mut words: [u32; 8] =
        std::array::from_fn(|i| u32::from_le_bytes(bytes[i * 4..(i + 1) * 4].try_into().unwrap()));
    let p = u64::from(KOALA_BEAR_PRIME);
    for &expected in &limbs {
        let mut carry: u64 = 0;
        for j in (0..8).rev() {
            let cur = (carry << 32) | u64::from(words[j]);
            words[j] = (cur / p) as u32;
            carry = cur % p;
        }
        assert_eq!(expected, carry as u32);
    }
}

#[test]
fn divmod_by_p_basic() {
    let mut acc = [u64::from(KOALA_BEAR_PRIME) + 5, 0, 0, 0];
    assert_eq!(divmod_by_p_in_place(&mut acc), 5);
    assert_eq!(acc, [1, 0, 0, 0]);

    let mut acc = [0, 1, 0, 0]; // 2^64
    let p = u128::from(KOALA_BEAR_PRIME);
    let r = divmod_by_p_in_place(&mut acc);
    assert_eq!(u128::from(r), (1u128 << 64) % p);
    assert_eq!(u128::from(acc[0]), (1u128 << 64) / p);
    assert_eq!(acc[1], 0);
}

#[test]
fn compose_limbs_inverse_of_decompose_for_canonical_limbs() {
    // Limbs in [0, P) round trip through bytes only when the byte buffer
    // can hold the full P^N_LIMBS range (i.e., n_bytes * 8 >= n_limbs *
    // log2(P)). Public key (8 F / 31 B) and signature (601 F / 2329 B)
    // satisfy this; messages (9 F / 32 B) intentionally do not — message
    // decoding is one-way, since 2^256 < P^9.
    for &(n_limbs, n_bytes) in &[
        (PUBLIC_KEY_LEN_FE, PUBLIC_KEY_BYTES_LEN),
        (SIGNATURE_LEN_FE, SIGNATURE_BYTES_LEN),
    ] {
        let limbs: Vec<u32> = (0..n_limbs as u32)
            .map(|i| (i.wrapping_mul(2654435761).wrapping_add(13)) % KOALA_BEAR_PRIME)
            .collect();
        let bytes = compose_limbs(&limbs, n_bytes);
        let decoded = decompose_bytes(&bytes, n_limbs);
        assert_eq!(decoded, limbs, "n_limbs={n_limbs} n_bytes={n_bytes}");
    }
}

// ---------------------------------------------------------------------------
// Message: high-level wrapper returning [F; 9].
// ---------------------------------------------------------------------------

#[test]
fn message_to_field_elements_zero() {
    let fes = message_to_field_elements(&[0u8; MESSAGE_BYTES_LEN]).expect("decode");
    for f in &fes {
        assert_eq!(*f, F::ZERO);
    }
}

#[test]
fn message_to_field_elements_one() {
    let mut bytes = [0u8; MESSAGE_BYTES_LEN];
    bytes[0] = 1;
    let fes = message_to_field_elements(&bytes).expect("decode");
    assert_eq!(fes[0].as_canonical_u32(), 1);
    for f in &fes[1..] {
        assert_eq!(*f, F::ZERO);
    }
}

#[test]
fn message_wrong_length_rejected() {
    assert!(message_to_field_elements(&[0u8; MESSAGE_BYTES_LEN - 1]).is_err());
    assert!(message_to_field_elements(&[0u8; MESSAGE_BYTES_LEN + 1]).is_err());
    assert!(message_to_field_elements(&[]).is_err());
}

// ---------------------------------------------------------------------------
// Public key: round trip through XmssPublicKey.
// ---------------------------------------------------------------------------

fn pk_with_root_from(seed_limbs: [u32; PUBLIC_KEY_LEN_FE]) -> XmssPublicKey {
    let merkle_root: [F; PUBLIC_KEY_LEN_FE] =
        std::array::from_fn(|i| F::new(seed_limbs[i] % KOALA_BEAR_PRIME));
    XmssPublicKey { merkle_root }
}

#[test]
fn public_key_round_trip_zero() {
    let pk = pk_with_root_from([0; PUBLIC_KEY_LEN_FE]);
    let bytes = public_key_to_bytes(&pk);
    assert_eq!(bytes, [0u8; PUBLIC_KEY_BYTES_LEN]);
    let decoded = public_key_from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.merkle_root, pk.merkle_root);
}

#[test]
fn public_key_round_trip_random_canonical() {
    let pk = pk_with_root_from(std::array::from_fn(|i| {
        ((i as u32).wrapping_mul(2654435761).wrapping_add(89)) % KOALA_BEAR_PRIME
    }));
    let bytes = public_key_to_bytes(&pk);
    let decoded = public_key_from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.merkle_root, pk.merkle_root);
}

#[test]
fn public_key_round_trip_max() {
    let pk = pk_with_root_from([KOALA_BEAR_PRIME - 1; PUBLIC_KEY_LEN_FE]);
    let bytes = public_key_to_bytes(&pk);
    let decoded = public_key_from_bytes(&bytes).expect("decode");
    assert_eq!(decoded.merkle_root, pk.merkle_root);
}

#[test]
fn public_key_wrong_length_rejected() {
    assert!(public_key_from_bytes(&[0u8; PUBLIC_KEY_BYTES_LEN - 1]).is_err());
    assert!(public_key_from_bytes(&[0u8; PUBLIC_KEY_BYTES_LEN + 1]).is_err());
    assert!(public_key_from_bytes(&[]).is_err());
}

// ---------------------------------------------------------------------------
// Signature: round trip through XmssSignature.
// ---------------------------------------------------------------------------

fn signature_with_canonical_limbs(seed: u32) -> XmssSignature {
    let limb_at = |i: usize| -> F {
        F::new(((i as u32).wrapping_mul(2654435761).wrapping_add(seed)) % KOALA_BEAR_PRIME)
    };
    let chain_tips: [[F; PUBLIC_KEY_LEN_FE]; V] =
        std::array::from_fn(|i| std::array::from_fn(|j| limb_at(i * PUBLIC_KEY_LEN_FE + j)));
    let randomness_base = V * PUBLIC_KEY_LEN_FE;
    let randomness: [F; RANDOMNESS_LEN_FE] = std::array::from_fn(|i| limb_at(randomness_base + i));
    let merkle_proof: Vec<[F; PUBLIC_KEY_LEN_FE]> = (0..LOG_LIFETIME)
        .map(|i| {
            let base = V * PUBLIC_KEY_LEN_FE + RANDOMNESS_LEN_FE + i * PUBLIC_KEY_LEN_FE;
            std::array::from_fn(|j| limb_at(base + j))
        })
        .collect();
    // A canonical slot fits in 32 bits but is split into two 16-bit
    // halves on the wire; pick a value that exercises both halves.
    let slot = seed ^ 0xDEAD_BEEF;
    XmssSignature {
        wots_signature: WotsSignature {
            chain_tips,
            randomness,
        },
        merkle_proof,
        slot,
    }
}

fn signatures_equal(a: &XmssSignature, b: &XmssSignature) -> bool {
    a.wots_signature.chain_tips == b.wots_signature.chain_tips
        && a.wots_signature.randomness == b.wots_signature.randomness
        && a.merkle_proof == b.merkle_proof
        && a.slot == b.slot
}

#[test]
fn signature_round_trip_zero() {
    let sig = signature_with_canonical_limbs(0);
    // Rebuild a sig with all zeros explicitly.
    let zero_sig = XmssSignature {
        wots_signature: WotsSignature {
            chain_tips: [[F::ZERO; PUBLIC_KEY_LEN_FE]; V],
            randomness: [F::ZERO; RANDOMNESS_LEN_FE],
        },
        merkle_proof: vec![[F::ZERO; PUBLIC_KEY_LEN_FE]; LOG_LIFETIME],
        slot: 0,
    };
    let bytes = signature_to_bytes(&zero_sig);
    assert_eq!(bytes, [0u8; SIGNATURE_BYTES_LEN]);
    let decoded = signature_from_bytes(&bytes).expect("decode");
    assert!(signatures_equal(&zero_sig, &decoded));
    let _ = sig; // suppress unused var
}

#[test]
fn signature_round_trip_random_canonical() {
    let sig = signature_with_canonical_limbs(0xc0ffee);
    let bytes = signature_to_bytes(&sig);
    let decoded = signature_from_bytes(&bytes).expect("decode");
    assert!(signatures_equal(&sig, &decoded));
}

#[test]
fn signature_wrong_length_rejected() {
    assert!(signature_from_bytes(&vec![0u8; SIGNATURE_BYTES_LEN - 1]).is_err());
    assert!(signature_from_bytes(&vec![0u8; SIGNATURE_BYTES_LEN + 1]).is_err());
}

// ---------------------------------------------------------------------------
// Non-canonical encodings: byte buffers whose little-endian integer
// is >= P^N for the target limb count must be rejected, not silently
// truncated. All-0xFF buffers are above the canonical range for both
// the public key (P^8 < 2^248) and the signature (P^601 < 2^18631 <
// 2^18632).
// ---------------------------------------------------------------------------

#[test]
fn decompose_bytes_canonical_accepts_round_tripped_limbs() {
    for &(n_limbs, n_bytes) in &[
        (PUBLIC_KEY_LEN_FE, PUBLIC_KEY_BYTES_LEN),
        (SIGNATURE_LEN_FE, SIGNATURE_BYTES_LEN),
    ] {
        let limbs: Vec<u32> = (0..n_limbs as u32)
            .map(|i| (i.wrapping_mul(2654435761).wrapping_add(13)) % KOALA_BEAR_PRIME)
            .collect();
        let bytes = compose_limbs(&limbs, n_bytes);
        let decoded =
            decompose_bytes_canonical(&bytes, n_limbs).expect("round-tripped bytes are canonical");
        assert_eq!(decoded, limbs, "n_limbs={n_limbs}");
    }
}

#[test]
fn decompose_bytes_canonical_rejects_overflow() {
    for &(n_limbs, n_bytes) in &[
        (PUBLIC_KEY_LEN_FE, PUBLIC_KEY_BYTES_LEN),
        (SIGNATURE_LEN_FE, SIGNATURE_BYTES_LEN),
    ] {
        let bytes = vec![0xFFu8; n_bytes];
        assert_eq!(
            decompose_bytes_canonical(&bytes, n_limbs),
            Err(DecodeError::NonCanonicalEncoding),
            "n_limbs={n_limbs}"
        );
    }
}

#[test]
fn public_key_non_canonical_rejected() {
    let bytes = [0xFFu8; PUBLIC_KEY_BYTES_LEN];
    assert_eq!(
        public_key_from_bytes(&bytes),
        Err(DecodeError::NonCanonicalEncoding)
    );
}

#[test]
fn signature_non_canonical_rejected() {
    let bytes = vec![0xFFu8; SIGNATURE_BYTES_LEN];
    assert_eq!(
        signature_from_bytes(&bytes),
        Err(DecodeError::NonCanonicalEncoding)
    );
}

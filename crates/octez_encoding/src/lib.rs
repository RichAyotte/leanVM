// SPDX-FileCopyrightText: 2026 Nomadic Labs <contact@nomadic-labs.com>
//
// XMSS encoding for the leanMultisig FFI: maps the upstream
// [`XmssPublicKey`] / [`XmssSignature`] types and the FFI message buffer
// to/from canonical little-endian byte buffers.
//
// The math is base-`P` decomposition (mirrors `int_to_base_p` in
// `leanSpec/src/lean_spec/subspecs/xmss/utils.py`) of a flat sequence of
// canonical KoalaBear field elements:
//
// - **Public key**: 8 F (Merkle root) <-> **31** bytes
// - **Signature**: 601 F (`V*8` chain tips + 7 randomness + `LOG_LIFETIME*8`
//   Merkle path + 2 slot) <-> **2329** bytes
// - **Message**: 32 bytes -> 9 F (decode-only — caller chooses the input
//   integer; the high range above `P^9` is unreachable since
//   `2^256 < P^9`)
//
// Decoding is canonical: a byte buffer whose little-endian integer is
// >= `P^N` (i.e., outside the range representable by `N` KoalaBear limbs)
// is rejected with [`DecodeError::NonCanonicalEncoding`] rather than
// silently truncating the high overflow. The message decoder never hits
// this case structurally (`2^256 < P^9`).

use backend::{KoalaBear as F, PrimeField32};
use xmss::{LOG_LIFETIME, RANDOMNESS_LEN_FE, V, WotsSignature, XmssPublicKey, XmssSignature};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// KoalaBear prime: `2^31 - 2^24 + 1`. Each emitted limb is in `[0, P)`.
pub const KOALA_BEAR_PRIME: u32 = 0x7f00_0001;

/// Length, in bytes, of the message buffer.
pub const MESSAGE_BYTES_LEN: usize = 32;

/// Number of field elements emitted from a message buffer; matches
/// `MSG_LEN_FE = 9` in the leanMultisig PROD config.
pub const MESSAGE_LEN_FE: usize = 9;

/// Number of field elements in an XMSS public key (the Merkle root).
/// Matches `DIGEST_SIZE = 8` in the upstream `xmss` crate.
pub const PUBLIC_KEY_LEN_FE: usize = 8;

/// Length, in bytes, of an XMSS public key. Equals
/// `ceil(8 * 31 / 8) = 31`, the densest packing of an 8-element
/// KoalaBear digest.
pub const PUBLIC_KEY_BYTES_LEN: usize = 31;

/// Number of field elements in an XMSS signature: WOTS chain tips
/// (`V * DIGEST_SIZE = 42 * 8 = 336`), WOTS randomness
/// (`RANDOMNESS_LEN_FE = 7`), the Merkle authentication path
/// (`LOG_LIFETIME * DIGEST_SIZE = 32 * 8 = 256`), and the slot
/// (2 KoalaBear field elements: 16-bit low and high halves).
pub const SIGNATURE_LEN_FE: usize = 601;

/// Length, in bytes, of an XMSS signature. Equals
/// `ceil(601 * 31 / 8) = 2329`.
pub const SIGNATURE_BYTES_LEN: usize = 2329;

/// `DIGEST_SIZE` in the upstream `xmss` crate is `pub(crate)`, so we
/// pin it here. The compile-time check below catches divergence.
const DIGEST_SIZE: usize = 8;

const _: () = assert!(MESSAGE_LEN_FE == xmss::MESSAGE_LEN_FE);
const _: () = assert!(PUBLIC_KEY_LEN_FE == DIGEST_SIZE);
const _: () = assert!(SIGNATURE_LEN_FE == xmss::SIG_SIZE_FE);
const _: () = assert!(
    SIGNATURE_LEN_FE == V * DIGEST_SIZE + RANDOMNESS_LEN_FE + LOG_LIFETIME * DIGEST_SIZE + 2
);

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Returned by the high-level decoders.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    /// Input byte slice has the wrong length for its caller.
    InvalidInputLength,
    /// Input bytes encode an integer `>= P^N`: the high overflow has no
    /// representation in the canonical limb space and would otherwise be
    /// silently dropped. Only reachable from public-key and signature
    /// decoding (the message decoder is structurally safe).
    NonCanonicalEncoding,
}

// ---------------------------------------------------------------------------
// Low-level base-`P` math.
//
// Exposed publicly so callers (e.g. the FFI) can perform encoding /
// decoding without going through the high-level wrappers below.
// ---------------------------------------------------------------------------

/// Divide a non-negative integer (stored as a little-endian `u64` slice)
/// by `KOALA_BEAR_PRIME` in place; return the remainder. Schoolbook long
/// division: walk limbs from most-significant to least-significant,
/// carrying the partial remainder forward. The intermediate `cur` fits
/// in `u128` since `carry < P < 2^32`.
pub fn divmod_by_p_in_place(acc: &mut [u64]) -> u32 {
    let p = u128::from(KOALA_BEAR_PRIME);
    let mut carry: u128 = 0;
    for i in (0..acc.len()).rev() {
        let cur = (carry << 64) | u128::from(acc[i]);
        acc[i] = (cur / p) as u64;
        carry = cur % p;
    }
    carry as u32
}

/// Decompose a `bytes`-byte little-endian integer into `n_limbs`
/// canonical KoalaBear field-element limbs (each in `[0, P)`) via
/// base-`P` extraction. Any input that exceeds `P^n_limbs` has its
/// high overflow silently truncated; use [`decompose_bytes_canonical`]
/// when round-trip integrity matters.
pub fn decompose_bytes(bytes: &[u8], n_limbs: usize) -> Vec<u32> {
    let n_words = bytes.len().div_ceil(8).max(1);
    let mut acc: Vec<u64> = vec![0; n_words];
    for (i, &b) in bytes.iter().enumerate() {
        acc[i / 8] |= u64::from(b) << ((i % 8) * 8);
    }
    let mut out = Vec::with_capacity(n_limbs);
    for _ in 0..n_limbs {
        out.push(divmod_by_p_in_place(&mut acc));
    }
    out
}

/// Same as [`decompose_bytes`] but rejects inputs encoding an integer
/// `>= P^n_limbs`. After extracting `n_limbs` limbs the remaining
/// accumulator must be zero; otherwise the input has no canonical limb
/// representation and we return [`DecodeError::NonCanonicalEncoding`]
/// rather than discarding the overflow.
pub fn decompose_bytes_canonical(bytes: &[u8], n_limbs: usize) -> Result<Vec<u32>, DecodeError> {
    let n_words = bytes.len().div_ceil(8).max(1);
    let mut acc: Vec<u64> = vec![0; n_words];
    for (i, &b) in bytes.iter().enumerate() {
        acc[i / 8] |= u64::from(b) << ((i % 8) * 8);
    }
    let mut out = Vec::with_capacity(n_limbs);
    for _ in 0..n_limbs {
        out.push(divmod_by_p_in_place(&mut acc));
    }
    if acc.iter().any(|&w| w != 0) {
        return Err(DecodeError::NonCanonicalEncoding);
    }
    Ok(out)
}

/// Compose `n_bytes` little-endian bytes from a sequence of canonical
/// KoalaBear field-element limbs via base-`P` reconstruction
/// (`acc = sum_{i>=0} limbs[i] * P^i`). Caller must ensure `n_bytes >=
/// ceil(n_limbs * log2(P) / 8)` (typically `ceil(n_limbs * 31 / 8)`);
/// otherwise the result wraps and a debug assertion fires.
pub fn compose_limbs(limbs: &[u32], n_bytes: usize) -> Vec<u8> {
    let p = u128::from(KOALA_BEAR_PRIME);
    let n_words = n_bytes.div_ceil(8).max(1);
    let mut acc: Vec<u64> = vec![0; n_words];
    for &limb in limbs.iter().rev() {
        let mut carry: u128 = u128::from(limb);
        for word in acc.iter_mut() {
            let prod = u128::from(*word) * p + carry;
            *word = prod as u64;
            carry = prod >> 64;
        }
        debug_assert_eq!(carry, 0, "compose overflow: buffer too small");
    }
    let mut out = vec![0u8; n_bytes];
    for (i, b) in out.iter_mut().enumerate() {
        *b = (acc[i / 8] >> ((i % 8) * 8)) as u8;
    }
    out
}

// ---------------------------------------------------------------------------
// High-level XMSS API
// ---------------------------------------------------------------------------

/// Decode 32 message bytes into the 9 KoalaBear field elements expected
/// by the upstream signer. Any 32-byte input is valid (since
/// `2^256 < P^9`), so only the length check can fail.
pub fn message_to_field_elements(bytes: &[u8]) -> Result<[F; MESSAGE_LEN_FE], DecodeError> {
    if bytes.len() != MESSAGE_BYTES_LEN {
        return Err(DecodeError::InvalidInputLength);
    }
    let limbs = decompose_bytes(bytes, MESSAGE_LEN_FE);
    let mut out: [F; MESSAGE_LEN_FE] = [F::new(0); MESSAGE_LEN_FE];
    for (i, &limb) in limbs.iter().enumerate() {
        out[i] = F::new(limb);
    }
    Ok(out)
}

/// Inverse of [`message_to_field_elements`]: re-encode 9 KoalaBear field
/// elements back into the canonical 32-byte message form. Only round-trips
/// values that originated from a 32-byte input (since `2^256 < P^9`, only
/// a subset of `[F; 9]` tuples maps back into the byte range; values
/// outside it would overflow). The aggregator preserves messages
/// unchanged, so this is safe for messages flowing back through the FFI.
pub fn message_from_field_elements(msg: &[F; MESSAGE_LEN_FE]) -> [u8; MESSAGE_BYTES_LEN] {
    let limbs: [u32; MESSAGE_LEN_FE] = std::array::from_fn(|i| msg[i].as_canonical_u32());
    let v = compose_limbs(&limbs, MESSAGE_BYTES_LEN);
    let mut out = [0u8; MESSAGE_BYTES_LEN];
    out.copy_from_slice(&v);
    out
}

/// Encode an XMSS public key (Merkle root, 8 F) as 31 canonical bytes.
pub fn public_key_to_bytes(pk: &XmssPublicKey) -> [u8; PUBLIC_KEY_BYTES_LEN] {
    let limbs: [u32; PUBLIC_KEY_LEN_FE] =
        std::array::from_fn(|i| pk.merkle_root[i].as_canonical_u32());
    let v = compose_limbs(&limbs, PUBLIC_KEY_BYTES_LEN);
    let mut out = [0u8; PUBLIC_KEY_BYTES_LEN];
    out.copy_from_slice(&v);
    out
}

/// Decode 31 bytes into an XMSS public key. Rejects non-canonical
/// inputs (integer `>= P^8`) with [`DecodeError::NonCanonicalEncoding`].
pub fn public_key_from_bytes(bytes: &[u8]) -> Result<XmssPublicKey, DecodeError> {
    if bytes.len() != PUBLIC_KEY_BYTES_LEN {
        return Err(DecodeError::InvalidInputLength);
    }
    let limbs = decompose_bytes_canonical(bytes, PUBLIC_KEY_LEN_FE)?;
    let merkle_root: [F; DIGEST_SIZE] = std::array::from_fn(|i| F::new(limbs[i]));
    Ok(XmssPublicKey { merkle_root })
}

/// Encode an XMSS signature (`chain_tips ++ randomness ++ merkle_proof ++
/// slot_lo ++ slot_hi`, flattened to 601 F) as 2329 canonical bytes.
pub fn signature_to_bytes(sig: &XmssSignature) -> [u8; SIGNATURE_BYTES_LEN] {
    let limbs = flatten_signature_to_limbs(sig);
    let v = compose_limbs(&limbs, SIGNATURE_BYTES_LEN);
    let mut out = [0u8; SIGNATURE_BYTES_LEN];
    out.copy_from_slice(&v);
    out
}

/// Decode 2329 bytes into an XMSS signature. Rejects non-canonical
/// inputs (integer `>= P^601`, or a slot limb that does not fit in
/// 16 bits) with [`DecodeError::NonCanonicalEncoding`].
pub fn signature_from_bytes(bytes: &[u8]) -> Result<XmssSignature, DecodeError> {
    if bytes.len() != SIGNATURE_BYTES_LEN {
        return Err(DecodeError::InvalidInputLength);
    }
    let limbs = decompose_bytes_canonical(bytes, SIGNATURE_LEN_FE)?;
    signature_from_limbs(&limbs)
}

// ---------------------------------------------------------------------------
// Struct flattening (private helpers)
// ---------------------------------------------------------------------------

fn flatten_signature_to_limbs(sig: &XmssSignature) -> [u32; SIGNATURE_LEN_FE] {
    let mut out = [0u32; SIGNATURE_LEN_FE];
    let mut idx = 0;
    for digest in &sig.wots_signature.chain_tips {
        for f in digest.iter() {
            out[idx] = f.as_canonical_u32();
            idx += 1;
        }
    }
    for f in &sig.wots_signature.randomness {
        out[idx] = f.as_canonical_u32();
        idx += 1;
    }
    for digest in &sig.merkle_proof {
        for f in digest.iter() {
            out[idx] = f.as_canonical_u32();
            idx += 1;
        }
    }
    // Slot as 2 limbs: low 16 bits, high 16 bits. Fits in two KoalaBear FE
    // (each < 2^31), matching `slot_to_field_elements` in `xmss::wots`.
    out[idx] = sig.slot & 0xFFFF;
    out[idx + 1] = (sig.slot >> 16) & 0xFFFF;
    out
}

fn signature_from_limbs(limbs: &[u32]) -> Result<XmssSignature, DecodeError> {
    debug_assert_eq!(limbs.len(), SIGNATURE_LEN_FE);
    let chain_tips: [[F; DIGEST_SIZE]; V] = std::array::from_fn(|i| {
        let base = i * DIGEST_SIZE;
        std::array::from_fn(|j| F::new(limbs[base + j]))
    });
    let rand_base = V * DIGEST_SIZE;
    let randomness: [F; RANDOMNESS_LEN_FE] = std::array::from_fn(|i| F::new(limbs[rand_base + i]));
    let proof_base = V * DIGEST_SIZE + RANDOMNESS_LEN_FE;
    let merkle_proof: Vec<[F; DIGEST_SIZE]> = (0..LOG_LIFETIME)
        .map(|i| {
            let base = proof_base + i * DIGEST_SIZE;
            std::array::from_fn(|j| F::new(limbs[base + j]))
        })
        .collect();
    let slot_base = proof_base + LOG_LIFETIME * DIGEST_SIZE;
    let slot_lo = limbs[slot_base];
    let slot_hi = limbs[slot_base + 1];
    // Reject non-canonical slot encodings: each half must fit in 16 bits,
    // matching how the prover splits a u32 slot in `slot_to_field_elements`.
    if slot_lo > 0xFFFF || slot_hi > 0xFFFF {
        return Err(DecodeError::NonCanonicalEncoding);
    }
    let slot = slot_lo | (slot_hi << 16);
    Ok(XmssSignature {
        wots_signature: WotsSignature {
            chain_tips,
            randomness,
        },
        merkle_proof,
        slot,
    })
}

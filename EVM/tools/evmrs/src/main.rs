//! Native helpers for the LeanEVM conform suite.
//!
//! CLI contract (mirrors the python scripts this replaces): arguments are
//! bare hex strings (no 0x), the result is printed to stdout as bare hex
//! with no trailing newline, and any failure prints the literal string
//! `error`. Exit code is 0 in both cases; a non-zero exit only signals
//! misuse (unknown subcommand / malformed invocation).

use std::io::Write;

fn out(s: &str) {
    print!("{s}");
    std::io::stdout().flush().ok();
}

fn err() -> ! {
    out("error");
    std::process::exit(0);
}

fn unhex(s: &str) -> Vec<u8> {
    match hex::decode(s.trim()) {
        Ok(v) => v,
        Err(_) => err(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(String::as_str).unwrap_or("");
    match cmd {
        "rip160" => rip160(&args[2..]),
        "recover" => recover(&args[2..]),
        "bn-add" => bn_add(&args[2..]),
        "bn-mul" => bn_mul(&args[2..]),
        "snarkv" => snarkv(&args[2..]),
        "point-eval" => point_eval(&args[2..]),
        "trie-root" => trie_root(&args[2..]),
        "state-root" => state_root(&args[2..]),
        _ => {
            eprintln!("usage: evmrs <rip160|recover|bn-add|bn-mul|snarkv|point-eval|trie-root|state-root> ...");
            std::process::exit(2);
        }
    }
}

/// `rip160 <data-hex>` → 32-byte left-padded RIPEMD-160 digest.
fn rip160(args: &[String]) {
    use ripemd::{Digest, Ripemd160};
    let data = unhex(args.first().map(String::as_str).unwrap_or(""));
    let digest = Ripemd160::digest(&data);
    let mut padded = [0u8; 32];
    padded[12..].copy_from_slice(&digest);
    out(&hex::encode(padded));
}

/// `recover <msghash> <v(32B)> <r(32B)> <s(32B)>` → 64-byte uncompressed pubkey (no 0x04).
/// `v` is the 0/1 recovery id, big-endian padded (as the Lean side sends it).
fn recover(args: &[String]) {
    use k256::ecdsa::{RecoveryId, Signature, VerifyingKey};
    use k256::elliptic_curve::scalar::IsHigh;
    if args.len() != 4 {
        err();
    }
    let msg = unhex(&args[0]);
    let v_bytes = unhex(&args[1]);
    let r = unhex(&args[2]);
    let s = unhex(&args[3]);
    if msg.len() != 32 {
        err();
    }
    let v = match v_bytes.iter().rev().next() {
        Some(&b) if v_bytes.iter().rev().skip(1).all(|&x| x == 0) && b <= 1 => b,
        _ => err(),
    };
    let mut r32 = [0u8; 32];
    let mut s32 = [0u8; 32];
    if r.len() > 32 || s.len() > 32 {
        err();
    }
    r32[32 - r.len()..].copy_from_slice(&r);
    s32[32 - s.len()..].copy_from_slice(&s);
    let mut sig = match Signature::from_scalars(r32, s32) {
        Ok(sig) => sig,
        Err(_) => err(),
    };
    let mut recid = v;
    // Recovery with a high-s signature is equivalent to recovery with the
    // normalized signature and a flipped parity bit.
    if bool::from(sig.s().is_high()) {
        sig = sig.normalize_s().unwrap_or(sig);
        recid ^= 1;
    }
    let recid = match RecoveryId::from_byte(recid) {
        Some(r) => r,
        None => err(),
    };
    match VerifyingKey::recover_from_prehash(&msg, &sig, recid) {
        Ok(vk) => {
            let point = vk.to_encoded_point(false);
            out(&hex::encode(&point.as_bytes()[1..65]));
        }
        Err(_) => err(),
    }
}

fn bn_fq(bytes32: &[u8]) -> bn::Fq {
    if bytes32.len() != 32 {
        err();
    }
    match bn::Fq::from_slice(bytes32) {
        Ok(v) => v,
        Err(_) => err(), // ≥ field prime
    }
}

fn bn_g1(x: bn::Fq, y: bn::Fq) -> bn::G1 {
    use bn::Group;
    if x == bn::Fq::zero() && y == bn::Fq::zero() {
        return bn::G1::zero();
    }
    match bn::AffineG1::new(x, y) {
        Ok(p) => p.into(),
        Err(_) => err(), // not on curve
    }
}

fn g1_out(p: bn::G1) {
    use bn::Group;
    let mut buf = [0u8; 64];
    if let Some(affine) = bn::AffineG1::from_jacobian(p) {
        affine.x().to_big_endian(&mut buf[0..32]).unwrap();
        affine.y().to_big_endian(&mut buf[32..64]).unwrap();
    }
    out(&hex::encode(buf));
}

/// `bn-add <x0> <y0> <x1> <y1>` (each 32B hex) → 64-byte point.
fn bn_add(args: &[String]) {
    if args.len() != 4 {
        err();
    }
    let p0 = bn_g1(bn_fq(&unhex(&args[0])), bn_fq(&unhex(&args[1])));
    let p1 = bn_g1(bn_fq(&unhex(&args[2])), bn_fq(&unhex(&args[3])));
    g1_out(p0 + p1);
}

/// `bn-mul <x0> <y0> <n>` (each 32B hex) → 64-byte point. Scalar is NOT
/// reduced-checked: any 256-bit value is a valid multiplier.
fn bn_mul(args: &[String]) {
    if args.len() != 3 {
        err();
    }
    let p = bn_g1(bn_fq(&unhex(&args[0])), bn_fq(&unhex(&args[1])));
    let n_bytes = unhex(&args[2]);
    if n_bytes.len() != 32 {
        err();
    }
    let n = bn::arith::U256::from_slice(&n_bytes).unwrap_or_else(|_| err());
    let scalar = bn::Fr::new_mul_factor(n);
    g1_out(p * scalar);
}

/// `snarkv <data>` — data is k*192 bytes of (G1, G2) pairs → 32-byte 0/1.
fn snarkv(args: &[String]) {
    use bn::{AffineG2, Fq2, G2, Group, Gt};
    let data = unhex(args.first().map(String::as_str).unwrap_or(""));
    if data.len() % 192 != 0 {
        err();
    }
    let mut pairs = Vec::new();
    for chunk in data.chunks(192) {
        let x = bn_fq(&chunk[0..32]);
        let y = bn_fq(&chunk[32..64]);
        // EVM encoding: G2 coordinates come imaginary-part first.
        let x_i = bn_fq(&chunk[64..96]);
        let x_r = bn_fq(&chunk[96..128]);
        let y_i = bn_fq(&chunk[128..160]);
        let y_r = bn_fq(&chunk[160..192]);
        let g1 = bn_g1(x, y);
        let x2 = Fq2::new(x_r, x_i);
        let y2 = Fq2::new(y_r, y_i);
        let g2: G2 = if x2 == Fq2::zero() && y2 == Fq2::zero() {
            G2::zero()
        } else {
            match AffineG2::new(x2, y2) {
                Ok(p) => p.into(),
                Err(_) => err(),
            }
        };
        pairs.push((g1, g2));
    }
    let ok = bn::pairing_batch(&pairs) == Gt::one();
    let mut buf = [0u8; 32];
    buf[31] = ok as u8;
    out(&hex::encode(buf));
}

/// `point-eval <data>` — 192 bytes: versioned_hash | z | y | commitment | proof
/// → FIELD_ELEMENTS_PER_BLOB(32B) ++ BLS_MODULUS(32B) on success.
///
/// Direct single-point KZG verification — `e(C − [y]₁, [1]₂) = e(π, [τ−z]₂)` —
/// needs only the ceremony's `[τ]₂` point (embedded below), not the full
/// 4096-point trusted setup, so there is no per-process setup parse.
fn point_eval(args: &[String]) {
    use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
    use sha2::{Digest, Sha256};

    /// `[τ]₂` from the Ethereum KZG ceremony (g2_values[1] of the canonical
    /// trusted setup), compressed.
    const TAU_G2: &str = "b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2";

    fn scalar_be(b: &[u8]) -> Scalar {
        let mut le = [0u8; 32];
        for i in 0..32 {
            le[i] = b[31 - i];
        }
        Option::<Scalar>::from(Scalar::from_bytes(&le)).unwrap_or_else(|| err())
    }
    fn g1(b: &[u8]) -> G1Affine {
        let bytes: [u8; 48] = b.try_into().unwrap_or_else(|_| err());
        Option::<G1Affine>::from(G1Affine::from_compressed(&bytes)).unwrap_or_else(|| err())
    }

    let data = unhex(args.first().map(String::as_str).unwrap_or(""));
    if data.len() != 192 {
        err();
    }
    let versioned_hash = &data[0..32];
    let z = scalar_be(&data[32..64]);
    let y = scalar_be(&data[64..96]);
    let commitment = g1(&data[96..144]);
    let proof = g1(&data[144..192]);

    let mut expected = Sha256::digest(&data[96..144]);
    expected[0] = 0x01;
    if versioned_hash != expected.as_slice() {
        err();
    }

    let tau_bytes: [u8; 96] = hex::decode(TAU_G2).unwrap().try_into().unwrap();
    let tau_g2 = Option::<G2Affine>::from(G2Affine::from_compressed(&tau_bytes)).unwrap();

    // e(C - [y]G₁, [1]₂) == e(π, [τ]₂ - [z]G₂)
    let lhs_g1 = G1Affine::from(G1Projective::from(commitment) - G1Projective::generator() * y);
    let rhs_g2 = G2Affine::from(G2Projective::from(tau_g2) - G2Projective::generator() * z);
    if pairing(&lhs_g1, &G2Affine::generator()) != pairing(&proof, &rhs_g2) {
        err();
    }
    // FIELD_ELEMENTS_PER_BLOB = 4096, BLS_MODULUS — fixed return per EIP-4844.
    out(concat!(
        "0000000000000000000000000000000000000000000000000000000000001000",
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
    ));
}

/// Merkle-Patricia trie root of (key, value) leaf pairs, with the python
/// `trie_set` semantics: later writes win, empty values are absent.
fn mpt_root(mut pairs: Vec<(Vec<u8>, Vec<u8>)>) -> [u8; 32] {
    use alloy_trie::{HashBuilder, Nibbles};
    // Later writes win (python trie_set overwrites), then sort by key as
    // HashBuilder requires strictly increasing insertion order.
    pairs.reverse();
    pairs.sort_by(|a, b| a.0.cmp(&b.0));
    pairs.dedup_by(|a, b| a.0 == b.0);
    let mut hb = HashBuilder::default();
    for (k, v) in &pairs {
        if !v.is_empty() {
            hb.add_leaf(Nibbles::unpack(k), v);
        }
    }
    hb.root().0
}

/// `trie-root <input-file> <n>` — input file holds `n` (key, value) pairs as
/// alternating hex lines; computes the unsecured Merkle-Patricia trie root.
fn trie_root(args: &[String]) {
    if args.len() != 2 {
        err();
    }
    let content = std::fs::read_to_string(&args[0]).unwrap_or_else(|_| err());
    let n: usize = args[1].parse().unwrap_or_else(|_| err());
    let mut lines = content.lines();
    let mut pairs: Vec<(Vec<u8>, Vec<u8>)> = Vec::with_capacity(n);
    for _ in 0..n {
        let k = unhex(lines.next().unwrap_or_else(|| err()));
        let v = unhex(lines.next().unwrap_or_else(|| err()));
        pairs.push((k, v));
    }
    out(&hex::encode(mpt_root(pairs)));
}

/// RLP encoding of a byte string, appended to `out`.
fn rlp_str(b: &[u8], out: &mut Vec<u8>) {
    if b.len() == 1 && b[0] < 0x80 {
        out.push(b[0]);
    } else if b.len() <= 55 {
        out.push(0x80 + b.len() as u8);
        out.extend_from_slice(b);
    } else {
        let lb = b.len().to_be_bytes();
        let lb = &lb[lb.iter().position(|&x| x != 0).unwrap()..];
        out.push(0xb7 + lb.len() as u8);
        out.extend_from_slice(lb);
        out.extend_from_slice(b);
    }
}

/// RLP list header for an already-encoded payload, prepended into a fresh buffer.
fn rlp_list(payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(payload.len() + 4);
    if payload.len() <= 55 {
        out.push(0xc0 + payload.len() as u8);
    } else {
        let lb = payload.len().to_be_bytes();
        let lb = &lb[lb.iter().position(|&x| x != 0).unwrap()..];
        out.push(0xf7 + lb.len() as u8);
        out.extend_from_slice(lb);
    }
    out.extend_from_slice(payload);
    out
}

/// `state-root <input-file>` — computes the secured state trie root over whole
/// accounts in ONE process (the per-account storage roots and the account RLP
/// leaves included), replacing one `trie-root` spawn per contract account.
///
/// Input file, all values bare hex, one per line:
/// ```text
/// A                     -- number of accounts
/// then A times:
///   keccak(address)     -- 32 bytes
///   nonce               -- minimal big-endian (empty line for 0)
///   balance             -- minimal big-endian
///   keccak(code)        -- 32 bytes
///   S                   -- number of storage entries
///   then S times:
///     keccak(slot)      -- 32 bytes
///     rlp(value)        -- RLP of the minimal big-endian value
/// ```
fn state_root(args: &[String]) {
    if args.len() != 1 {
        err();
    }
    let content = std::fs::read_to_string(&args[0]).unwrap_or_else(|_| err());
    let mut lines = content.lines();
    let mut next = || lines.next().unwrap_or_else(|| err());
    let n_accounts: usize = next().trim().parse().unwrap_or_else(|_| err());
    let mut state_pairs: Vec<(Vec<u8>, Vec<u8>)> = Vec::with_capacity(n_accounts);
    for _ in 0..n_accounts {
        let addr_hash = unhex(next());
        let nonce = unhex(next());
        let balance = unhex(next());
        let code_hash = unhex(next());
        let n_storage: usize = next().trim().parse().unwrap_or_else(|_| err());
        let mut storage_pairs: Vec<(Vec<u8>, Vec<u8>)> = Vec::with_capacity(n_storage);
        for _ in 0..n_storage {
            let k = unhex(next());
            let v = unhex(next());
            storage_pairs.push((k, v));
        }
        let storage_root = mpt_root(storage_pairs);
        // rlp([nonce, balance, storageRoot, codeHash])
        let mut payload = Vec::with_capacity(128);
        rlp_str(&nonce, &mut payload);
        rlp_str(&balance, &mut payload);
        rlp_str(&storage_root, &mut payload);
        rlp_str(&code_hash, &mut payload);
        state_pairs.push((addr_hash, rlp_list(&payload)));
    }
    out(&hex::encode(mpt_root(state_pairs)));
}

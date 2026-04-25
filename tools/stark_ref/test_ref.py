#!/usr/bin/env python3
"""Self-tests + cross-test-vector generator for the reference stack.

Run from repo root:
    python3 -m tools.stark_ref.test_ref

On success prints `PASS` followed by a block of cross-test vectors —
raw values / byte sequences that can be pasted into the Forth tests
(or embedded as known-answer constants) to confirm the two
implementations match.
"""

from __future__ import annotations

import sys

from .field import (
    P, G, BETA, HALF,
    bb_add, bb_sub, bb_mul, bb_inv, bb_pow, bb_root_of_unity,
    bb4_add, bb4_mul, bb4_inv, bb4_pow, bb4_half, bb4_zero, bb4_one, bb4_eq,
    bb_to_bytes, bb4_to_bytes, bb4_from_bytes, bb_to_bb4,
)
from .transcript import Transcript
from .merkle     import MerkleTree, merkle_verify, blake2s_32
from .fri        import fri_prove, fri_verify


FAILED = 0

def check(cond: bool, msg: str) -> None:
    global FAILED
    if not cond:
        print(f"FAIL: {msg}", file=sys.stderr)
        FAILED += 1

# ══════════════════════════════════════════════════════════════════════
# Base-field sanity
# ══════════════════════════════════════════════════════════════════════

def test_bb() -> None:
    check(P == 2**31 - 2**27 + 1,          "P value")
    check(HALF == (P + 1) // 2,             "HALF value")
    check(bb_add(P - 1, 1) == 0,            "bb add wrap")
    check(bb_sub(0, 1) == P - 1,            "bb sub wrap")
    check(bb_mul(HALF, 2) == 1,             "HALF · 2 = 1")
    check(bb_mul(bb_inv(7), 7) == 1,        "inv(7) · 7 = 1")
    # Fermat: a^(p-1) = 1.
    check(bb_pow(12345, P - 1) == 1,        "Fermat on 12345")
    # Root of unity.
    omega = bb_root_of_unity(16)
    check(bb_pow(omega, 16) == 1,           "ω^16 = 1")
    check(bb_pow(omega, 8) != 1,            "ω primitive")

# ══════════════════════════════════════════════════════════════════════
# Extension field
# ══════════════════════════════════════════════════════════════════════

def test_bb4() -> None:
    ZERO, ONE = bb4_zero(), bb4_one()
    check(bb4_eq(bb4_add(ZERO, ZERO), ZERO), "bb4 0+0")
    check(bb4_eq(bb4_mul(ZERO, ONE),  ZERO), "bb4 0·1")
    check(bb4_eq(bb4_mul(ONE, ONE),   ONE),  "bb4 1·1")

    # x · x³ = x⁴ = β
    x  = (0, 1, 0, 0)
    x3 = (0, 0, 0, 1)
    check(bb4_eq(bb4_mul(x, x3), (BETA, 0, 0, 0)),   "x·x³ = β")
    # x² · x² = β
    x2 = (0, 0, 1, 0)
    check(bb4_eq(bb4_mul(x2, x2), (BETA, 0, 0, 0)),  "x²·x² = β")

    # Halving
    check(bb4_eq(bb4_half((2, 4, 6, 8)), (1, 2, 3, 4)), "bb4 halve evens")
    check(bb4_eq(bb4_half((1, 0, 0, 0)), (HALF, 0, 0, 0)), "bb4 halve 1")

    # Inverse
    a = (3, 5, 7, 11)
    inv = bb4_inv(a)
    check(bb4_eq(bb4_mul(a, inv), ONE), "bb4 a · a⁻¹ = 1")

    # Pow: (x+1)^4 mod (x^4 - β) — compute directly, compare with bb4_pow
    x_plus_1 = (1, 1, 0, 0)
    p2  = bb4_mul(x_plus_1, x_plus_1)
    p4  = bb4_mul(p2, p2)
    check(bb4_eq(bb4_pow(x_plus_1, 4), p4),  "bb4 pow 4")

# ══════════════════════════════════════════════════════════════════════
# Serialization round-trips
# ══════════════════════════════════════════════════════════════════════

def test_serialization() -> None:
    check(bb_to_bytes(0)   == b'\x00\x00\x00\x00',       "bb encode 0")
    check(bb_to_bytes(1)   == b'\x01\x00\x00\x00',       "bb encode 1")
    check(bb_to_bytes(P-1) == b'\x00\x00\x00\x78',       "bb encode p-1")
    a = (0xdeadbeef % P, 0x12345678 % P, 0xdeadd00d % P, 7)
    b = bb4_to_bytes(a)
    check(len(b) == 16,                                   "bb4 encode len")
    check(bb4_from_bytes(b) == a,                         "bb4 round-trip")

# ══════════════════════════════════════════════════════════════════════
# Transcript determinism and divergence
# ══════════════════════════════════════════════════════════════════════

def test_transcript() -> None:
    t1 = Transcript(b"STARK-v0")
    t2 = Transcript(b"STARK-v0")
    check(t1.squeeze32() == t2.squeeze32(),
          "same label → same first squeeze")

    t1 = Transcript(b"STARK-v0")
    t2 = Transcript(b"STARK-v1")
    check(t1.squeeze32() != t2.squeeze32(),
          "different labels → different squeeze")

    t1 = Transcript(b"t")
    a = t1.squeeze32()
    b = t1.squeeze32()
    check(a != b, "successive squeezes differ")

    t1 = Transcript(b"t"); t1.absorb(b"payload-A")
    t2 = Transcript(b"t"); t2.absorb(b"payload-B")
    check(t1.squeeze32() != t2.squeeze32(),
          "different absorb → different squeeze")

    # Challenge-BB is always < P.
    t = Transcript(b"bb")
    for _ in range(64):
        check(t.challenge_bb() < P, "challenge_bb < p")

# ══════════════════════════════════════════════════════════════════════
# Merkle tree + verifier
# ══════════════════════════════════════════════════════════════════════

\
# Convention: same leaf contents as tests/test_merkle.forth, so the
# Python cross-test vectors equal what Forth produces.  Leaf k holds
# bytes (64·k + i) & 0xFF for i in 0..63.
def _merkle_leaf_bytes(k: int) -> bytes:
    return bytes((64 * k + i) & 0xFF for i in range(64))


def test_merkle() -> None:
    leaf_bytes  = [_merkle_leaf_bytes(k) for k in range(4)]
    leaf_hashes = [blake2s_32(b) for b in leaf_bytes]
    tree = MerkleTree(leaf_hashes)
    check(tree.depth == 2, f"depth is 2, got {tree.depth}")

    for i in range(4):
        path = tree.open(i)
        check(merkle_verify(leaf_hashes[i], i, path, tree.root),
              f"verify leaf {i}")
        # Tamper: wrong index fails.
        bad_idx = (i + 1) & 3
        check(not merkle_verify(leaf_hashes[i], bad_idx, path, tree.root),
              f"leaf {i} with wrong index → reject")
        # Tampered root fails.
        check(not merkle_verify(leaf_hashes[i], i, path, b'\x00' * 32),
              f"leaf {i} with zero root → reject")

    # Depth-1 tree.
    small = MerkleTree(leaf_hashes[:2])
    check(small.depth == 1, "small tree depth")
    check(merkle_verify(leaf_hashes[0], 0, small.open(0), small.root),
          "small leaf 0")

    # Depth-0 (single leaf is the root).
    single = MerkleTree([leaf_hashes[0]])
    check(single.root == leaf_hashes[0], "single = root")
    check(single.depth == 0, "depth 0")
    check(merkle_verify(leaf_hashes[0], 0, [], single.root),
          "verify single-leaf tree")

# ══════════════════════════════════════════════════════════════════════
# Cross-test vectors — print fixed inputs + expected bytes so the Forth
# side can embed them as known-answer tests.
# ══════════════════════════════════════════════════════════════════════

def _hex(b: bytes) -> str:
    return ' '.join(f'{x:02x}' for x in b)

def emit_vectors() -> None:
    print()
    print("=" * 68)
    print("CROSS-TEST VECTORS (Forth ↔ Python)")
    print("=" * 68)

    print("\n[bb4 encoding]")
    for a in [(1, 2, 3, 4),
              (P - 1, P - 1, P - 1, P - 1),
              (0xdeadbeef % P, 0, HALF, BETA)]:
        print(f"  {a} → {_hex(bb4_to_bytes(a))}")

    print("\n[transcript — label='STARK-v0', no absorb, first squeeze]")
    t = Transcript(b"STARK-v0")
    print(f"  state0 = {_hex(t.squeeze32())}")

    print("\n[transcript — label='STARK-v0', absorb 'abc', first squeeze]")
    t = Transcript(b"STARK-v0"); t.absorb(b"abc")
    print(f"  state1 = {_hex(t.squeeze32())}")

    print("\n[transcript — label='bb-test', first 4 challenge_bb]")
    t = Transcript(b"bb-test")
    for i in range(4):
        print(f"  c{i} = {t.challenge_bb()}")

    print("\n[merkle — matches tests/test_merkle.forth leaf pattern]")
    leaf_bytes  = [_merkle_leaf_bytes(k) for k in range(4)]
    leaf_hashes = [blake2s_32(b) for b in leaf_bytes]
    tree = MerkleTree(leaf_hashes)
    for i, h in enumerate(leaf_hashes):
        print(f"  leaf-hash {i} = {_hex(h)}")
    print(f"  root        = {_hex(tree.root)}")
    for i in range(4):
        path = tree.open(i)
        print(f"  path[{i}]:")
        for j, s in enumerate(path):
            print(f"    level {j}: {_hex(s)}")

# ══════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════════════
# FRI prover ↔ verifier round-trip + tamper rejection
# ══════════════════════════════════════════════════════════════════════

def _eval_bb_poly(coeffs, x: int) -> int:
    """Horner's method, low-degree-first coefficients in F_p."""
    result = 0
    for c in reversed(coeffs):
        result = bb_add(bb_mul(result, x), c)
    return result


def test_fri() -> None:
    # Polynomial p(X) = 1 + 2X + 3X² + 4X³ — degree 3, fits in trace size 4.
    # n0=16 / blowup=4 / 2 folds → final domain |D_2| = 4 with implicit
    # degree bound 1.  The prover sends 4 final-layer evaluations and the
    # verifier insists they all match (low-degree check), AND each query's
    # fold-result equals the final-poly value at the queried residue.
    coeffs = [1, 2, 3, 4]
    trace_size = 4
    blowup     = 4
    n0         = trace_size * blowup        # 16
    final_size = 4                          # |D_L| after 2 folds
    num_queries = 16                        # every position queried — deterministic catch

    omega         = bb_root_of_unity(n0)
    domain_offset = G                       # G is a non-unit-coset shift
    # Evaluate p on D₀ and lift to BB⁴.
    x = domain_offset
    base_evals = []
    for _ in range(n0):
        base_evals.append(_eval_bb_poly(coeffs, x))
        x = bb_mul(x, omega)
    values = [bb_to_bb4(v) for v in base_evals]

    # ── Round-trip: prove → verify → accept ──
    pt = Transcript(b"FRI-test")
    proof = fri_prove(values, domain_offset, omega, pt,
                      num_queries=num_queries, final_size=final_size)
    vt = Transcript(b"FRI-test")
    ok = fri_verify(proof, n0, domain_offset, omega, vt,
                    num_queries=num_queries, final_size=final_size)
    check(ok, "FRI: low-degree poly verifies")

    # ── Sanity on the proof shape ──
    expected_layers = 0
    sz = n0
    while sz > final_size:
        expected_layers += 1
        sz //= 2
    check(len(proof.layer_roots)    == expected_layers, "FRI layers count")
    check(len(proof.final_poly)     == final_size,      "FRI final poly size")
    check(len(proof.query_openings) == num_queries,     "FRI per-query openings")
    for q_open in proof.query_openings:
        check(len(q_open) == expected_layers, "FRI per-layer opening count")

    # ── Tamper 1: mutate one byte of the final polynomial. ──
    bad_proof = _clone_proof(proof)
    fp = list(bad_proof.final_poly)
    fp[0] = (bb_add(fp[0][0], 1),) + fp[0][1:]
    bad_proof.final_poly = fp
    vt = Transcript(b"FRI-test")
    ok = fri_verify(bad_proof, n0, domain_offset, omega, vt,
                    num_queries=num_queries, final_size=final_size)
    check(not ok, "FRI: tampered final_poly → reject")

    # ── Tamper 2: flip a bit in a layer root. ──
    bad_proof = _clone_proof(proof)
    if bad_proof.layer_roots:
        r = bytearray(bad_proof.layer_roots[0])
        r[0] ^= 0x01
        bad_proof.layer_roots[0] = bytes(r)
    vt = Transcript(b"FRI-test")
    ok = fri_verify(bad_proof, n0, domain_offset, omega, vt,
                    num_queries=num_queries, final_size=final_size)
    check(not ok, "FRI: flipped root bit → reject")

    # ── Tamper 3: change a leaf opening byte. ──
    bad_proof = _clone_proof(proof)
    leaf, path = bad_proof.query_openings[0][0]
    bad_leaf = bytearray(leaf); bad_leaf[0] ^= 0x01
    bad_proof.query_openings[0][0] = (bytes(bad_leaf), path)
    vt = Transcript(b"FRI-test")
    ok = fri_verify(bad_proof, n0, domain_offset, omega, vt,
                    num_queries=num_queries, final_size=final_size)
    check(not ok, "FRI: tampered leaf → reject")

    # ── Tamper 4: feed a HIGH-degree input.  With high probability the
    #              folds become inconsistent and verification fails.
    rogue = list(values)
    rogue[5] = bb4_add(rogue[5], (1, 0, 0, 0))   # break low-degree-ness
    pt = Transcript(b"FRI-test")
    rogue_proof = fri_prove(rogue, domain_offset, omega, pt,
                            num_queries=num_queries, final_size=final_size)
    vt = Transcript(b"FRI-test")
    ok = fri_verify(rogue_proof, n0, domain_offset, omega, vt,
                    num_queries=num_queries, final_size=final_size)
    # Soundness: with 6 queries, blowup 4, the per-query rejection
    # probability is ≥ 1/4 once the input is far from any low-degree
    # polynomial.  6 queries → ≥ 1 - (3/4)^6 ≈ 82% chance of catching.
    # The tamper above isn't even close to a polynomial, so reject is
    # essentially certain here.
    check(not ok, "FRI: high-degree input → reject")


def _clone_proof(proof):
    """Deep-ish copy adequate for tamper tests (lists/tuples are immutable)."""
    from copy import deepcopy
    return deepcopy(proof)


def main() -> int:
    test_bb()
    test_bb4()
    test_serialization()
    test_transcript()
    test_merkle()
    test_fri()

    if FAILED == 0:
        print("PASS")
        emit_vectors()
        return 0
    print(f"FAIL ({FAILED} failures)")
    return 1

if __name__ == "__main__":
    sys.exit(main())

"""FRI prover + verifier (binary fold, BabyBear⁴ throughout).

Mirrors the algebraic kernel in src/fri.forth and chains it with the
Merkle / transcript modules.  This is a reference implementation —
correctness over performance.

Protocol summary
----------------
Inputs (agreed by both parties out of band):
    n0              size of the LDE domain D₀ (power of two)
    final_size      where folding stops (power of two, < n0)
    num_queries     soundness target
    domain_offset   base-field offset of the coset D₀
    domain_omega    primitive n0-th root of unity in F_p

Prover loop:
    f₀ on D₀
    repeat:
        leaves[k]   = pack(f_i[k], f_i[k + n_i/2])         k ∈ [0, n_i/2)
        root_i      = MerkleTree(blake2s(leaf)).root
        transcript ← absorb(root_i)
        α_i         ← transcript.challenge_bb4()
        for j in [0, n_i/2):
            x        = g_i · η_i^j
            f_{i+1}[j] = (f_i[j] + f_i[j+n_i/2])/2
                       + α_i · (f_i[j] − f_i[j+n_i/2]) / (2x)
        n_{i+1}     = n_i/2;  g_{i+1} = g_i²;  η_{i+1} = η_i²
    while n_i > final_size
    final_poly = current f
    transcript ← absorb(final_poly bytes)
    query positions   ← num_queries × challenge_u32 mod n0

Verifier:
    Replay transcript to derive α_i and query positions.
    For each query q₀:
        walk down the layers, opening one Merkle leaf per layer; at
        each layer check (a) the Merkle path opens to root_i and
        (b) the value at the queried position equals what the
        previous layer's fold produced.  At the bottom, compare with
        final_poly[q_L].

Pair packing
------------
At each layer the Merkle tree has n_i/2 leaves; leaf k encodes the
pair  (f_i[k], f_i[k + n_i/2])  as 32 bytes (= 2 × BB⁴ at 16 bytes
each).  The pair (k, k+n_i/2) corresponds to antipodal evaluations
f(x) and f(−x), exactly the two values one fold step needs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Tuple

from .field import (
    bb_mul, bb_pow, bb_inv,
    bb4_add, bb4_sub, bb4_mul, bb4_eq,
    bb4_scalar_mul, bb4_half,
    bb4_to_bytes, bb4_from_bytes,
    bb_to_bb4,
)
from .merkle    import MerkleTree, merkle_verify, blake2s_32
from .transcript import Transcript


# ── Proof dataclass ───────────────────────────────────────────────────

@dataclass
class FriProof:
    """Concrete data the prover sends to the verifier."""
    layer_roots: List[bytes]                              # one per fold layer
    final_poly:  List[Tuple[int, int, int, int]]          # BB⁴ values, length = final_size
    # query_openings[q][layer] = (leaf_bytes (32), path (depth × 32-byte hashes))
    query_openings: List[List[Tuple[bytes, List[bytes]]]]


# ── Helpers ───────────────────────────────────────────────────────────

def _pack_pair(v_lo, v_hi) -> bytes:
    """Pack two BB⁴ elements into a 32-byte Merkle-leaf payload."""
    return bb4_to_bytes(v_lo) + bb4_to_bytes(v_hi)


def _unpack_pair(b: bytes) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
    assert len(b) == 32
    return bb4_from_bytes(b[:16]), bb4_from_bytes(b[16:])


def _fold_one(v_lo, v_hi, alpha, x: int):
    """One scalar fold step:
        folded = ((v_lo + v_hi) + α · (v_lo − v_hi) · x⁻¹) · ½

    Mirrors src/fri.forth's `fri-fold-step`, but takes x rather than
    x⁻¹ (we compute the base-field inverse on the spot).
    """
    sum_  = bb4_add(v_lo, v_hi)
    diff  = bb4_sub(v_lo, v_hi)
    x_inv = bb_inv(x)
    t     = bb4_scalar_mul(diff, x_inv)
    t     = bb4_mul(t, alpha)
    return bb4_half(bb4_add(sum_, t))


# ── Prover ────────────────────────────────────────────────────────────

def fri_prove(values: List[Tuple[int, int, int, int]],
              domain_offset: int,
              domain_omega: int,
              transcript: Transcript,
              num_queries: int,
              final_size: int) -> FriProof:
    """Generate a FRI proof that `values` (BB⁴ evaluations on a coset of
    F_p with shift `domain_offset` and primitive root `domain_omega`)
    correspond to a polynomial of degree < |values| / blowup, by folding
    until the residual domain has size `final_size`.

    `transcript` is consumed (its state advances) — the verifier must
    receive it in the same starting state.
    """
    n0 = len(values)
    assert n0 & (n0 - 1) == 0,             "n0 must be a power of 2"
    assert final_size & (final_size - 1) == 0
    assert n0 > final_size,                "must fold at least once"
    # Sanity: pow(omega, n0) == 1.
    assert bb_pow(domain_omega, n0) == 1, "omega is not n0-th root of unity"

    layer_roots:    List[bytes]               = []
    layer_trees:    List[MerkleTree]          = []
    layer_values:   List[List[Tuple[int, ...]]] = []
    alphas:         List[Tuple[int, ...]]     = []

    current_values  = values
    current_size    = n0
    current_offset  = domain_offset
    current_omega   = domain_omega

    while current_size > final_size:
        half = current_size // 2

        # Build pair-packed leaves and Merkle tree.
        leaves_bytes = [
            _pack_pair(current_values[k], current_values[k + half])
            for k in range(half)
        ]
        leaf_hashes = [blake2s_32(b) for b in leaves_bytes]
        tree = MerkleTree(leaf_hashes)

        layer_roots.append(tree.root)
        layer_trees.append(tree)
        layer_values.append(current_values)

        transcript.absorb(tree.root)
        alpha = transcript.challenge_bb4()
        alphas.append(alpha)

        # Fold f_i → f_{i+1}.
        next_values: List[Tuple[int, ...]] = []
        x = current_offset                           # x_0 = offset
        for j in range(half):
            v_lo = current_values[j]
            v_hi = current_values[j + half]
            next_values.append(_fold_one(v_lo, v_hi, alpha, x))
            x = bb_mul(x, current_omega)

        current_values = next_values
        current_offset = bb_mul(current_offset, current_offset)
        current_omega  = bb_mul(current_omega,  current_omega)
        current_size   = half

    # Final polynomial: send remaining values directly.
    final_poly = current_values
    transcript.absorb(b''.join(bb4_to_bytes(v) for v in final_poly))

    # Sample query positions.
    query_positions = [transcript.challenge_u32() % n0
                       for _ in range(num_queries)]

    # Build per-query openings.
    query_openings: List[List[Tuple[bytes, List[bytes]]]] = []
    for q0 in query_positions:
        per_query: List[Tuple[bytes, List[bytes]]] = []
        q    = q0
        size = n0
        for tree, vals in zip(layer_trees, layer_values):
            half = size // 2
            pair_index = q % half
            leaf_bytes = _pack_pair(vals[pair_index], vals[pair_index + half])
            per_query.append((leaf_bytes, tree.open(pair_index)))
            q    = q % half
            size = half
        query_openings.append(per_query)

    return FriProof(layer_roots=layer_roots,
                    final_poly=final_poly,
                    query_openings=query_openings)


# ── Verifier ──────────────────────────────────────────────────────────

def fri_verify(proof:                 FriProof,
               n0:                    int,
               domain_offset:         int,
               domain_omega:          int,
               transcript:            Transcript,
               num_queries:           int,
               final_size:            int,
               final_degree_bound:    int = 1) -> bool:
    """Verify a FRI proof.  Returns True iff every query passes.

    `final_degree_bound` is the implicit degree bound on the final
    polynomial (default 1 = "constant").  Folding halves the degree
    bound at each layer; with blowup ρ at layer 0 and L folds, the
    final domain has |D_L| = ρ · final_degree_bound and the prover's
    final-poly evaluations should fit a polynomial of that degree.

    For final_degree_bound = 1 the check reduces to "all final-layer
    evaluations are equal" — the polynomial must be a constant.
    """
    expected_layers = 0
    sz = n0
    while sz > final_size:
        expected_layers += 1
        sz //= 2

    if len(proof.layer_roots) != expected_layers:
        return False
    if len(proof.final_poly) != final_size:
        return False
    if len(proof.query_openings) != num_queries:
        return False

    # Low-degree check on the final polynomial.  This is what gives FRI
    # its soundness — a high-degree-input prover that folds honestly
    # ends up with non-constant final values, and we reject here.
    if final_degree_bound == 1:
        for v in proof.final_poly:
            if not bb4_eq(v, proof.final_poly[0]):
                return False
    else:
        # Generalized degree check (interpolate + drop high coefficients)
        # would go here.  Not needed for the prototype — extend when
        # final_degree_bound > 1 becomes a real use case.
        raise NotImplementedError(
            "fri_verify only supports final_degree_bound = 1 today")

    # Replay transcript.
    alphas: List[Tuple[int, ...]] = []
    for root in proof.layer_roots:
        transcript.absorb(root)
        alphas.append(transcript.challenge_bb4())
    transcript.absorb(b''.join(bb4_to_bytes(v) for v in proof.final_poly))

    query_positions = [transcript.challenge_u32() % n0
                       for _ in range(num_queries)]

    # Verify each query.
    for q_idx, q0 in enumerate(query_positions):
        openings = proof.query_openings[q_idx]
        if len(openings) != expected_layers:
            return False

        q       = q0
        size    = n0
        offset  = domain_offset
        omega   = domain_omega
        v_chain = None       # value carried down from previous layer's fold

        for layer_idx, (leaf_bytes, path) in enumerate(openings):
            half       = size // 2
            pair_index = q % half

            # 1. Merkle authentication.
            if len(leaf_bytes) != 32:
                return False
            leaf_hash = blake2s_32(leaf_bytes)
            if not merkle_verify(leaf_hash, pair_index, path,
                                 proof.layer_roots[layer_idx]):
                return False

            v_lo, v_hi = _unpack_pair(leaf_bytes)

            # 2. The value at the queried position in this layer is one
            #    of (v_lo, v_hi); pick by the within-pair offset.
            within_pair = 0 if q < half else 1
            v_at_q_here = v_lo if within_pair == 0 else v_hi

            # 3. Consistency with the previous layer's fold (skipped for layer 0).
            if v_chain is not None and not bb4_eq(v_chain, v_at_q_here):
                return False

            # 4. Fold to get the value the next layer must reveal.
            x = bb_mul(offset, bb_pow(omega, pair_index))
            v_chain = _fold_one(v_lo, v_hi, alphas[layer_idx], x)

            # Advance to the next layer.
            q       = q % half
            size    = half
            offset  = bb_mul(offset, offset)
            omega   = bb_mul(omega,  omega)

        # 5. The last folded value must match the directly-revealed
        #    final polynomial at q's image in the final domain.
        if not bb4_eq(v_chain, proof.final_poly[q]):
            return False

    return True

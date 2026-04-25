"""Reference STARK prover/verifier matching the Forth verifier's primitives.

Mirrors:
    src/field.forth       → field.py   (BabyBear + BB⁴)
    src/transcript.forth  → transcript.py (Fiat-Shamir over BLAKE2s)
    src/merkle.forth      → merkle.py  (binary Merkle over BLAKE2s)
    src/fri.forth         → fri.py     (coming next turn)

Byte-level serialization is chosen to match the Forth side exactly (LE
u32 per BabyBear element, BB⁴ as 4 concatenated LE u32s, Merkle and
hash input identical to what blake2s.forth + merkle.forth produce).

Slow by design — this is a correctness / cross-check reference, not a
performance prover.
"""

from .field import (
    P, G, BETA,
    bb_add, bb_sub, bb_neg, bb_mul, bb_inv, bb_pow, bb_root_of_unity,
    bb4_add, bb4_sub, bb4_neg, bb4_mul, bb4_inv, bb4_pow,
    bb4_scalar_mul, bb4_half,
    bb4_zero, bb4_one, bb4_eq, bb_to_bb4,
    bb_to_bytes, bb_from_bytes, bb4_to_bytes, bb4_from_bytes,
)

from .transcript import Transcript
from .merkle    import MerkleTree, merkle_verify, blake2s_32
from .fri       import FriProof, fri_prove, fri_verify

__all__ = [
    'P', 'G', 'BETA',
    'bb_add', 'bb_sub', 'bb_neg', 'bb_mul', 'bb_inv', 'bb_pow',
    'bb_root_of_unity',
    'bb4_add', 'bb4_sub', 'bb4_neg', 'bb4_mul', 'bb4_inv', 'bb4_pow',
    'bb4_scalar_mul', 'bb4_half',
    'bb4_zero', 'bb4_one', 'bb4_eq', 'bb_to_bb4',
    'bb_to_bytes', 'bb_from_bytes', 'bb4_to_bytes', 'bb4_from_bytes',
    'Transcript',
    'MerkleTree', 'merkle_verify', 'blake2s_32',
    'FriProof', 'fri_prove', 'fri_verify',
]

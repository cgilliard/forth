"""Binary Merkle tree over BLAKE2s.

Mirrors src/merkle.forth:

    * Caller supplies pre-hashed leaves (32 bytes each).
    * Inner node = blake2s(left || right), 64-byte input.
    * No domain-separation byte (matches Plonky3 / Winterfell / RISC Zero).
    * Path layout: an array of sibling hashes level 0 (closest to leaf)
      first, depth hashes total.  At each level, bit i of the leaf index
      chooses whether the running hash is the left (bit = 0) or right
      (bit = 1) child.
"""

from __future__ import annotations

import hashlib
from typing import List


def blake2s_32(data: bytes) -> bytes:
    """One-block BLAKE2s → 32-byte digest."""
    return hashlib.blake2s(data).digest()


class MerkleTree:
    """Build a binary Merkle tree over a list of 32-byte leaf hashes.

    The caller is responsible for hashing leaf *data* into a 32-byte
    commitment before passing it in — this matches merkle.forth, which
    only knows about 32-byte values.
    """

    def __init__(self, leaf_hashes: List[bytes]):
        n = len(leaf_hashes)
        assert n >= 1 and (n & (n - 1)) == 0, \
            f"leaf count must be power of 2 (got {n})"
        assert all(len(h) == 32 for h in leaf_hashes), \
            "all leaves must be 32 bytes"
        self.levels: List[List[bytes]] = [list(leaf_hashes)]
        while len(self.levels[-1]) > 1:
            prev = self.levels[-1]
            self.levels.append([
                blake2s_32(prev[i] + prev[i + 1])
                for i in range(0, len(prev), 2)
            ])
        self.root: bytes = self.levels[-1][0]
        self.depth: int = len(self.levels) - 1

    def open(self, index: int) -> List[bytes]:
        """Return the sibling-hash path from leaf `index` up to (but not
        including) the root — `depth` entries, level 0 first."""
        assert 0 <= index < len(self.levels[0]), \
            f"index {index} out of range"
        path: List[bytes] = []
        for level in self.levels[:-1]:
            path.append(level[index ^ 1])
            index //= 2
        return path


def merkle_verify(leaf_hash: bytes, index: int, path: List[bytes],
                  root: bytes) -> bool:
    """Walk the running hash from `leaf_hash` up, hashing one sibling
    per level, and check that the top matches `root`."""
    assert len(leaf_hash) == 32
    assert len(root) == 32
    current = leaf_hash
    for sibling in path:
        assert len(sibling) == 32
        if index & 1 == 0:
            current = blake2s_32(current + sibling)
        else:
            current = blake2s_32(sibling + current)
        index //= 2
    return current == root

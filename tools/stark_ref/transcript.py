"""Fiat-Shamir transcript over BLAKE2s.

Mirrors src/transcript.forth:

    state (32 bytes) starts as blake2s(label).
    absorb(data)         : state = blake2s(state || data)
    squeeze32()          : state = blake2s(state); return state
    challenge_bb()       : squeeze32 repeatedly, read low 4 bytes as LE
                           u32, rejection-sample until < p.
    challenge_bb4()      : four independent challenge_bb() draws.
    challenge_u32()      : squeeze32, read low 4 bytes as LE u32, no
                           rejection (for FRI query indices).

The Forth side reads only the first 4 bytes of each 32-byte squeeze;
this Python implementation does exactly the same so test vectors line
up byte-for-byte.
"""

from __future__ import annotations

import hashlib
from typing import Tuple

from .field import P


class Transcript:
    __slots__ = ('state',)

    def __init__(self, label: bytes):
        self.state = hashlib.blake2s(label).digest()

    def absorb(self, data: bytes) -> None:
        self.state = hashlib.blake2s(self.state + data).digest()

    def squeeze32(self) -> bytes:
        """Advance the state by one blake2s and return the full 32-byte digest."""
        self.state = hashlib.blake2s(self.state).digest()
        return self.state

    def challenge_bb(self) -> int:
        """Rejection-sample a uniform element of F_p from the low 4 bytes
        of successive blake2s outputs."""
        while True:
            self.state = hashlib.blake2s(self.state).digest()
            u = int.from_bytes(self.state[:4], 'little')
            if u < P:
                return u

    def challenge_bb4(self) -> Tuple[int, int, int, int]:
        return (self.challenge_bb(),
                self.challenge_bb(),
                self.challenge_bb(),
                self.challenge_bb())

    def challenge_u32(self) -> int:
        """Sample a raw u32 (no rejection — for FRI query indices modulo N)."""
        self.state = hashlib.blake2s(self.state).digest()
        return int.from_bytes(self.state[:4], 'little')

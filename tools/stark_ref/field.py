"""BabyBear base field and BabyBear⁴ extension.

Mirrors src/field.forth:
    BabyBear prime p = 2^31 - 2^27 + 1 = 2013265921 = 0x78000001.
    Quartic extension: F_p[x] / (x^4 - β) with β = 11 (Plonky3 convention).

Representation:
    BB element:   a plain Python int in [0, p).
    BB⁴ element:  tuple (a0, a1, a2, a3)  representing  a0 + a1·x + a2·x² + a3·x³.

Serialization (matches the Forth verifier's native LE-u32 layout):
    BB:  4 bytes, little-endian.
    BB⁴: 16 bytes = 4 concatenated LE u32 components, a0 first.
"""

from typing import List, Tuple

# ── Constants ─────────────────────────────────────────────────────────

P = 2013265921                      # 2^31 - 2^27 + 1
G = 31                              # multiplicative generator (2-adicity 27)
BETA = 11                           # x^4 - 11 irreducible over F_p
HALF = (P + 1) // 2                 # 2^{-1} mod p = 1006632961

# ── BabyBear ──────────────────────────────────────────────────────────

def bb_add(a: int, b: int) -> int: return (a + b) % P
def bb_sub(a: int, b: int) -> int: return (a - b) % P
def bb_neg(a: int) -> int:         return (-a) % P
def bb_mul(a: int, b: int) -> int: return (a * b) % P

def bb_inv(a: int) -> int:
    if a == 0:
        raise ZeroDivisionError("bb_inv(0)")
    return pow(a, P - 2, P)

def bb_pow(a: int, n: int) -> int:
    return pow(a, n, P)

def bb_root_of_unity(n: int) -> int:
    """Primitive n-th root of unity in F_p.  n must be a power of 2 dividing p-1."""
    assert n > 0 and (n & (n - 1)) == 0, f"n must be a power of 2, got {n}"
    assert (P - 1) % n == 0, f"no n-th root of unity for n={n}"
    return bb_pow(G, (P - 1) // n)

# ── BabyBear⁴ ─────────────────────────────────────────────────────────

def bb4_zero() -> Tuple[int, int, int, int]: return (0, 0, 0, 0)
def bb4_one()  -> Tuple[int, int, int, int]: return (1, 0, 0, 0)

def bb_to_bb4(a: int) -> Tuple[int, int, int, int]:
    return (a % P, 0, 0, 0)

def bb4_eq(a, b) -> bool:
    return all(a[i] == b[i] for i in range(4))

def bb4_add(a, b):
    return tuple(bb_add(a[i], b[i]) for i in range(4))

def bb4_sub(a, b):
    return tuple(bb_sub(a[i], b[i]) for i in range(4))

def bb4_neg(a):
    return tuple(bb_neg(v) for v in a)

def bb4_mul(a, b):
    """Schoolbook multiplication modulo x^4 - β."""
    pp = [[bb_mul(a[i], b[j]) for j in range(4)] for i in range(4)]
    c0 = (pp[0][0] + BETA * (pp[1][3] + pp[2][2] + pp[3][1])) % P
    c1 = (pp[0][1] + pp[1][0] + BETA * (pp[2][3] + pp[3][2])) % P
    c2 = (pp[0][2] + pp[1][1] + pp[2][0] + BETA * pp[3][3]) % P
    c3 = (pp[0][3] + pp[1][2] + pp[2][1] + pp[3][0]) % P
    return (c0, c1, c2, c3)

def bb4_scalar_mul(a, s: int):
    """Multiply BB⁴ element by a base-field scalar (componentwise)."""
    return tuple(bb_mul(a[i], s) for i in range(4))

def bb4_half(a):
    """a · (1/2), matching fe-half in field.forth."""
    return bb4_scalar_mul(a, HALF)

def bb4_pow(a, n: int):
    """Square-and-multiply exponentiation in BB⁴."""
    result = bb4_one()
    base = a
    while n > 0:
        if n & 1:
            result = bb4_mul(result, base)
        base = bb4_mul(base, base)
        n >>= 1
    return result

def bb4_inv(a):
    """Inverse in BB⁴ via Fermat: a^{|F|-2} where |F| = p^4."""
    if bb4_eq(a, bb4_zero()):
        raise ZeroDivisionError("bb4_inv(0)")
    q = P ** 4
    return bb4_pow(a, q - 2)

# ── Serialization (LE u32) ────────────────────────────────────────────

def bb_to_bytes(a: int) -> bytes:
    assert 0 <= a < P, f"bb value out of range: {a}"
    return a.to_bytes(4, 'little')

def bb_from_bytes(b: bytes) -> int:
    v = int.from_bytes(b[:4], 'little')
    assert v < P, f"bytes decode to out-of-range bb: {v}"
    return v

def bb4_to_bytes(a) -> bytes:
    return b''.join(bb_to_bytes(v) for v in a)

def bb4_from_bytes(b: bytes) -> Tuple[int, int, int, int]:
    return tuple(bb_from_bytes(b[i*4:(i+1)*4]) for i in range(4))

# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""09 -- Zero is one bit: the empty configuration versus the point 0.

Classical problem.  Lebesgue measure gives {} and {0} the same value 0;
inside the measure the statements "nothing is there" and "the point 0 is
there" are the same null class.  The distinction must be put back by hand
(an atom, a Dirac mass, a NULL flag), and its cost is invisible to the
continuum: "how much does it cost to record the value 0?" has the
classical answer "nothing", which is wrong for every physical register.

Granular resolution (Chapter 16: thm:zero-one-bit, prop:info-register,
cor:info-zero-costs, prop:info-nullable, prop:info-erasure,
prop:info-observe-zero; Landauer remark in sec:information-landauer).
mu({}) = 0 < 2eps = mu({0}); the alternative costs exactly one bit; a
register for {0..M} needs ceil(log2(M+1)) bits, the "+1" being the zero;
a NULL-able field has M+2 states; erasing to 0 costs >= kT ln 2 per bit.
"""
from fractions import Fraction as F
from math import ceil, comb, log, log2


def Hb(p):
    return 0.0 if p in (0, 1) else -p * log2(p) - (1 - p) * log2(1 - p)


def min_bits(states):                      # smallest b with 2^b >= states (by search)
    b = 0
    while 2 ** b < states:
        b += 1
    return b


def main():
    eps = F(1, 2 * 10 ** 6)
    mu = lambda A: 2 * eps * len(A)
    assert mu(set()) == 0 < mu({0}) == 2 * eps                  # thm:zero-one-bit (i)
    assert min_bits(2) == 1 and min_bits(1) == 0                 # (ii), (iv)
    assert max(Hb(i / 1000) for i in range(1001)) == Hb(0.5) == 1.0   # (iii)
    print(f"mu({{}}) = {mu(set())},  mu({{0}}) = {mu({0})} = 2eps;  "
          f"telling them apart: {min_bits(2)} bit")
    print(f"\n{'M':>6} {'states 0..M':>11} {'bits':>5} {'ceil log2(M+1)':>15} {'+NULL':>6}")
    for M in [1, 2, 3, 7, 8, 255, 256, 10 ** 6]:
        b = min_bits(M + 1)
        assert b == ceil(log2(M + 1)) == M.bit_length()          # prop:info-register
        assert min_bits(M + 2) == ceil(log2(M + 2))              # prop:info-nullable
        print(f"{M:6d} {M + 1:11d} {b:5d} {ceil(log2(M + 1)):15d} {min_bits(M + 2):6d}")
    for b in range(1, 17):                                       # cor:info-zero-costs
        assert min_bits(2 ** b) == b and min_bits(2 ** b + 1) == b + 1
    # Pruning masks: n weights, s kept.  The zeros are not free: listing the
    # support needs log2(n+1) bits for s plus log2 C(n, s) for the positions.
    n = 1024
    print(f"\npruned layer, n = {n} weights: bits to record WHICH weights are zero")
    for s in [0, 1, 32, 512, 1024]:
        bits = log2(n + 1) + log2(comb(n, s))
        assert bits >= log2(n + 1) > 0                           # even s = 0 costs bits
        print(f"  s = {s:5d} kept: {bits:9.2f} bits  (n Hb(s/n) = {n * Hb(s / n):8.2f})")
    # Observing exactly 0 on a 3-digit display, X uniform on [-1,1] n L, 2eps = 1e-3
    m = 1000
    P0 = F(1, 2 * m + 1)
    e = F(1, 2 * m)
    assert P0 == e / (1 + e)                                     # prop:info-observe-zero
    print(f"\nP(X = 0.000) = 1/{2 * m + 1}, surprisal {log2(2 * m + 1):.2f} bits (same as 0.537)")
    # Landauer: erasing a register uniform on {0..M} to 0 lowers H by log2(M+1)
    kB, T = 1.380649e-23, 300.0                                  # J/K (exact SI), K
    E1 = kB * T * log(2)
    assert abs(E1 - 2.871e-21) < 1e-24
    meV = E1 / 1.602176634e-19 * 1e3
    print(f"Landauer at T = 300 K: kT ln2 = {E1:.4e} J = {meV:.2f} meV per bit")
    for M in [1, 255, 2 ** 32 - 1]:
        dH = log2(M + 1)                                         # prop:info-erasure
        assert dH >= 1
        print(f"  reset uniform {{0..{M}}} -> 0: dH = {dH:5.1f} bits, heat >= {E1 * dH:.3e} J")
    print("OK 09_zero_is_one_bit")


if __name__ == "__main__":
    main()

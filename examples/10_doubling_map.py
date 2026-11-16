# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""10 -- The doubling map: IEEE doubles are a dyadic lattice, and every orbit dies.

Classical problem.  For x -> 2x mod 1, Lebesgue-almost every orbit is dense
and equidistributed; the map is mixing with entropy log 2.  Yet every
floating-point orbit reaches 0 within about 53 steps.  Classically this is
an "artefact": the computed object is not the classical orbit, and the
classical theory says nothing about the object one actually computes (the
dyadic rationals are a null set that ergodic theory ignores).

Granular resolution (Chapter 17: thm:dyn-bit-shift, thm:dyn-collapse,
thm:dyn-last-bit, thm:dyn-one-bit-per-step; Problems solved, "Trustworthy
simulation of chaos").  On the dyadic lattice 2eps = 2^-K the map is
k -> 2k mod 2^K.  The orbit of k != 0 reaches 0 after exactly K - v2(k)
steps, through 1/2 at the penultimate step, and the state entropy falls by
exactly one bit per step.  A double in [1/2, 1) is m 2^-53, and 2x, 2x - 1
are exact, so IEEE doubling *is* the granular map with K = 53.
"""
from fractions import Fraction as F
import math
import random
import numpy as np


def v2(m):
    return (m & -m).bit_length() - 1


def float_orbit(x):
    orbit = [x]
    while x != 0.0:
        x = 2.0 * x
        if x >= 1.0:
            x -= 1.0                       # exact in IEEE arithmetic
        orbit.append(x)
    return orbit


def main():
    rng = random.Random(53)
    print(f"{'x0':>22} {'m = x0 2^53':>18} {'steps':>6} {'53 - v2(m)':>11}")
    for _ in range(6):
        x0 = 0.5 + rng.random() / 2                         # a double in [1/2, 1)
        m = int(F(x0) * 2 ** 53)
        assert F(x0) == F(m, 2 ** 53)
        orb = float_orbit(x0)
        assert len(orb) - 1 == 53 - v2(m) and orb[-2] == 0.5     # thm:dyn-collapse, last bit
        # the float orbit coincides with the exact Fraction orbit on the 2^-53 lattice
        k = m
        for x in orb:
            assert F(x) == F(k, 2 ** 53)
            k = 2 * k % 2 ** 53
        print(f"{x0!r:>22} {m:18d} {len(orb) - 1:6d} {53 - v2(m):11d}")
    # general doubles in (0,1): x = m 2^(e-53), m odd part decides
    for x0 in [0.1, 1 / 3, math.pi - 3, 2 ** -40]:
        mant, e = math.frexp(x0)                            # x0 = mant 2^e, mant in [1/2,1)
        m = int(mant * 2 ** 53)
        steps = (53 - e) - v2(m)
        assert len(float_orbit(x0)) - 1 == steps
        print(f"{x0!r:>22} reaches 0 after {steps} steps (= 53 - e - v2(m), e = {e})")
    # exhaustive dyadic lattice, K = 16: image sizes 2^(K-j), entropy K - j bits
    K = 16
    k = np.arange(2 ** K, dtype=np.int64)
    steps = np.where(k == 0, 0, K - np.array([v2(int(i)) if i else 0 for i in k]))
    state = k.copy()
    print(f"\nK = {K}: j, #image, H(state) bits")
    for j in range(K + 1):
        vals, counts = np.unique(state, return_counts=True)
        assert len(vals) == 2 ** (K - j) and np.all(counts == 2 ** j)  # thm:dyn-one-bit-per-step
        H = float(-(counts / 2 ** K * np.log2(counts / 2 ** K)).sum())
        assert abs(H - (K - j)) < 1e-12
        assert np.all((state == 0) == (steps <= j))             # zero iff 2^(K-j) | k
        if j in (0, 1, 2, K - 1, K):
            print(f"  {j:2d} {len(vals):6d} {abs(H):5.1f}")
        state = 2 * state % 2 ** K
    print("Classically a.e. orbit is dense; on the lattice every orbit ends at {0},")
    print("the one-cell state mu{0} = 2eps -- the last bit.")
    print("OK 10_doubling_map")


if __name__ == "__main__":
    main()

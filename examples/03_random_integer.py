# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""03 -- A uniformly random integer.

Classical problem.  There is no countably additive probability on N that
gives all singletons the same mass c: countable additivity forces
1 = sum_k c, which is 0 or infinity.  "Pick an integer uniformly at random"
has no classical model; statements such as "an integer is even with
probability 1/2" or "two integers are coprime with probability 6/pi^2"
are about natural densities (limits), not probabilities on a space.

Granular resolution (Chapter 13: thm:prob-uniform-integer,
thm:prob-density-shadow, ex:prob-integers).  The random integer of horizon
H is the uniform law on {1..H}.  Every integer has probability 1/H > 0;
P(m | X) = floor(H/m)/H, which is exactly 1/m when m | H (all m <= M when
H = M!); divisibility by distinct primes is exactly independent; the
coprimality probability is the exact rational (2 sum_{k<=H} phi(k) - 1)/H^2,
whose shadow is 6/pi^2; translation invariance holds up to an exact boundary
term of size 1/H.
"""
from fractions import Fraction as F
from math import factorial, gcd, pi, log
import numpy as np


def totients(n):
    phi = np.arange(n + 1, dtype=np.int64)
    for p in range(2, n + 1):
        if phi[p] == p:                      # p is prime
            phi[p::p] -= phi[p::p] // p
    return phi


def p_coprime(H, phi):
    return F(2 * int(phi[1:H + 1].sum()) - 1, H * H)


def main():
    M = 9
    H = factorial(M)                         # H = 9! = 362880
    assert F(1, H) > 0 and H * F(1, H) == 1          # every k has mass 1/H; total 1
    print(f"H = {M}! = {H}; P(X = k) = 1/H = {1 / H:.3e} for every k <= H")
    print(f"{'m':>3} {'P(m | X)':>12} {'1/m':>10} {'exact?':>7}")
    for m in [2, 3, 5, 7, 9, 10, 11, 13]:
        P = F(H // m, H)
        assert abs(P - F(1, m)) <= F(1, H)              # always within 1/H
        assert (P == F(1, m)) == (H % m == 0)           # exact iff m | H
        print(f"{m:3d} {float(P):12.9f} {1 / m:10.7f} {str(P == F(1, m)):>7}")
    for p, q in [(2, 3), (2, 7), (5, 7)]:              # exact independence
        assert F(H // (p * q), H) == F(H // p, H) * F(H // q, H)
    # shift defect: P(X+1 in A) - P(X in A) = (1_A(H) - 1_A(0))/H, X on {0..H-1}
    A = lambda k: k % 7 == 3 or k == H           # an arbitrary internal set
    lhs = F(sum(A(k + 1) for k in range(H)) - sum(A(k) for k in range(H)), H)
    assert lhs == F(int(A(H)) - int(A(0)), H)
    # coprimality: brute force for small H, totient formula for H = 9!
    phi = totients(H)
    for h in [1, 2, 10, 37]:
        brute = F(sum(gcd(x, y) == 1 for x in range(1, h + 1) for y in range(1, h + 1)), h * h)
        assert brute == p_coprime(h, phi)
    print(f"\n{'H':>8} {'P(gcd(X,Y)=1)':>15} {'- 6/pi^2':>11} {'log(H)/H':>10}")
    for h in [10, 100, 1000, 10 ** 4, 10 ** 5, H]:
        err = float(p_coprime(h, phi)) - 6 / pi ** 2
        assert abs(err) < 2 * log(h) / h                # O(log H / H), constant 2 here
        print(f"{h:8d} {float(p_coprime(h, phi)):15.10f} {err:11.2e} {log(h) / h:10.2e}")
    print("Classically: sum over k of c is 0 or infinity -- no uniform law on N.")
    print("OK 03_random_integer")


if __name__ == "__main__":
    main()

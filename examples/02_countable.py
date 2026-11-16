# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""02 -- Countable sets: the rationals of [0,1] on a factorial lattice.

Classical problem.  Lebesgue measure gives every countable set measure 0,
so Q n [0,1], a dense set meeting every interval, is indistinguishable
from the empty set (and from a single point).  "How large is the set of
rationals in [0,1]?" has only the answer 0 = leb({}) = leb({1/2}).

Granular resolution (Chapter 3: thm:countable-positive, thm:faithful).
Take 2*eps = 1/N with N = M!.  Every rational p/q with q <= M is a lattice
point, so the Farey set F_M = {p/q : 0 <= p <= q <= M} is a finite
(hyperfinite) set of lattice points, with mu(F_M) = |F_M| * 2eps > 0 and
mu(F_M) <= (M+1)^2 / M!.  Its shadow is 0: Lebesgue's value.  The internal
set *Q n [0,1] n Lattice is the whole lattice interval [0,1] (all lattice
points are rational), of measure 1 + 2eps.  A hyperfinite enumeration
A_H = {snap(a_j) : j < H} has mu(A_H) <= H * 2eps, with equality iff the
snapped values are distinct.
"""
from fractions import Fraction as F
from math import factorial, gcd


def farey(M):
    return {F(p, q) for q in range(1, M + 1) for p in range(q + 1)}


def farey_count(M):                       # 1 + sum_{q <= M} phi(q)
    return 1 + sum(1 for q in range(1, M + 1) for p in range(1, q + 1) if gcd(p, q) == 1)


def snap(x, N):                           # def:snap, nearest centre (ties up)
    return F(int(x * N + F(1, 2)) if x >= 0 else -int(-x * N + F(1, 2)), N)


def main():
    print(f"{'M':>3} {'N=M!':>10} {'|F_M|':>6} {'mu(F_M)':>12} {'(M+1)^2/M!':>12}")
    prev = None
    for M in range(2, 13):
        N, FM = factorial(M), farey(M)
        assert len(FM) == farey_count(M)
        assert all((x * N).denominator == 1 for x in FM)      # lattice points
        m = F(len(FM), N)
        assert F(1, N) <= m <= F((M + 1) ** 2, N)              # positive, small
        if M >= 4:
            assert prev is None or m < prev                    # shadow -> 0
            prev = m
        print(f"{M:3d} {N:10d} {len(FM):6d} {float(m):12.4e} {(M + 1) ** 2 / N:12.4e}")
    # Q n [0,1] n Lattice = [0,1] n Lattice (brute force for N = 5!)
    N = factorial(5)
    lattice01 = [F(k, N) for k in range(N + 1)]
    # every lattice point k/N is rational, so the trace of *Q is the whole of [0,1];
    # the trace of the irrationals is empty (thm:shadow)
    assert all(x.denominator <= N for x in lattice01)
    assert F(len(lattice01), N) == 1 + F(1, N)                # mu = 1 + 2eps
    print(f"\nmu(*Q n [0,1] n L) for N = 5!: {F(len(lattice01), N)} = 1 + 2eps")
    # Hyperfinite enumeration with repetitions: p/q, q = 1..Q, p = 0..q, snapped.
    M, Q = 6, 9                                # denominators 7, 8, 9 are not lattice
    N = factorial(M)
    seq = [snap(F(p, q), N) for q in range(1, Q + 1) for p in range(q + 1)]
    A = set(seq)
    H = len(seq)
    assert F(len(A), N) < F(H, N)              # repetitions: strict inequality
    seq_red = [x for x in dict.fromkeys(F(p, q) for q in range(1, M + 1) for p in range(q + 1))]
    assert F(len(set(seq_red)), N) == F(len(seq_red), N)     # distinct: equality
    print(f"A_H with H = {H} terms (q <= {Q}), N = {M}!: |A_H| = {len(A)}, "
          f"mu = {F(len(A), N)} < H*2eps = {F(H, N)}")
    print("Lebesgue: leb(Q n [0,1]) = 0 = leb({}); granular: mu > 0 = mu({}).")
    print("OK 02_countable")


if __name__ == "__main__":
    main()

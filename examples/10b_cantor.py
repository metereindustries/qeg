# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""10b -- Cantor: the Cantor set, Cantor dust and the diagonal argument, by counting.

Classical problem.  The Cantor set C is uncountable yet has Lebesgue
measure 0; its Cantor function is continuous, non-decreasing, constant on
every removed interval, and still climbs from 0 to 1.  Cantor dust C x C
has dimension 2 log 2/log 3 only as a limit.  The diagonal argument shows
that no list indexed by the naturals exhausts the binary sequences, but it
says nothing quantitative: "how many are missed?" has the answer
"uncountably many", a cardinal, not a number.

Granular resolution (Chapter 12, Fractal Geometry).  On the triadic
lattice of spacing 2eps = 3^-K (lattice point k means k 3^-K) the Cantor set
is the finite set C_K of indices whose K ternary digits are 0 or 2:
    #C_K = 2^K,  mu(C_K) = 2^K 3^-K = (2/3)^K > 0,
an exact positive content whose shadow (standard part, K infinite) is the
Lebesgue value 0.  The Cantor function is the counting function
#{c in C_K : c < x} / 2^K, an exact rational step function.  Cantor dust
has #(C_K x C_K) = 4^K = (2^K)^2, so its dimension at the granule is
exactly 2 log 2/log 3.  The diagonal argument becomes a finite, exact
statement: a list of K binary strings of length K misses exactly
2^K - #distinct rows >= 2^K - K strings, among them its diagonal.
"""
from fractions import Fraction
import itertools
import math
import random
import numpy as np


def cantor(K):
    """Sorted indices k in [0, 3^K) whose K ternary digits are all 0 or 2."""
    idx = np.zeros(1, dtype=np.int64)
    for i in range(K):
        idx = (idx[:, None] + np.array([0, 2], dtype=np.int64)[None, :] * 3 ** i).ravel()
    return np.sort(idx)


def part1():
    print("1. Cantor set C_K on the lattice 3^-K")
    print("    K    #C_K   mu = (2/3)^K")
    for K in range(1, 13):
        C = cantor(K)
        assert len(C) == 2 ** K and len(np.unique(C)) == 2 ** K
        mu = Fraction(len(C), 3 ** K)                    # count x 2eps
        assert mu == Fraction(2, 3) ** K and mu > 0
        if K in (1, 2, 3, 6, 12):
            print(f"   {K:2d} {len(C):7d}   {mu} = {float(mu):.6f}")
    # mu > 0 at every K, but below every standard positive bound: shadow 0
    mus = [Fraction(2, 3) ** K for K in range(1, 200)]
    assert all(m > 0 for m in mus) and all(a > b for a, b in zip(mus, mus[1:]))
    for n in (10, 10 ** 6, 10 ** 30):
        K = next(K for K, m in enumerate(mus, 1) if m < Fraction(1, n))
        print(f"   (2/3)^K < 1/{n:g} from K = {K}")
    print("   uncountable and Lebesgue-null classically; granularly 2^K points with exact")
    print("   positive content (2/3)^K, whose shadow is the Lebesgue value 0.")

    # devil's staircase: F(k) = #{c in C_K : c < k} / 2^K at every lattice point k
    K = 10
    C = cantor(K)
    k = np.arange(3 ** K + 1, dtype=np.int64)
    cnt = np.searchsorted(C, k, side="left")             # exact integer counts
    assert cnt[0] == 0 and cnt[-1] == 2 ** K
    assert np.all(np.diff(cnt) >= 0)                     # non-decreasing
    assert np.all(np.diff(cnt) <= 1)                     # steps of exactly 1/2^K
    third = 3 ** (K - 1)
    assert np.all(cnt[third:2 * third + 1] == 2 ** (K - 1))   # 1/2 on the middle third
    F = [Fraction(int(c), 2 ** K) for c in cnt[::3 ** 5]]
    assert all(f.denominator <= 2 ** K for f in F)
    assert abs(Fraction(int(cnt[3 ** K // 4]), 2 ** K) - Fraction(1, 3)) <= Fraction(1, 2 ** K)
    steps = int(np.count_nonzero(np.diff(cnt)))
    assert steps == 2 ** K                               # one jump per Cantor point
    print(f"   Cantor function, K = {K}: F(k) = #{{c < k}}/2^{K}, exact rationals,"
          f" {steps} jumps of 1/2^{K},")
    print(f"   F = 1/2 on the whole middle third [3^{K - 1}, 2*3^{K - 1}],"
          f" F(1/4) ~ F({3 ** K // 4}) = {Fraction(int(cnt[3 ** K // 4]), 2 ** K)}"
          f" (classical 1/3, within 1/2^{K})")


def part2():
    print("2. Cantor dust C_K x C_K")
    for K in (4, 6, 8):
        C = cantor(K)
        X, Y = np.repeat(C, len(C)), np.tile(C, len(C))
        assert len(np.unique(X * 3 ** K + Y)) == 4 ** K == (2 ** K) ** 2
        for j in range(K + 1):                           # every 3-adic scale
            assert len(np.unique((X // 3 ** j) * 3 ** K + Y // 3 ** j)) == 4 ** (K - j)
        d = math.log(4 ** K) / math.log(3 ** K)
        assert abs(d - 2 * math.log(2) / math.log(3)) < 1e-12
        print(f"   K = {K}: N = {4 ** K} = (2^{K})^2, N(3^j) = 4^(K-j) for all j,"
              f" dim = log N / log 3^K = {d:.6f}")
    print(f"   2 log2/log3 = {2 * math.log(2) / math.log(3):.6f}, exact at the granule")


def diagonal(rows):
    return tuple(1 - rows[i][i] for i in range(len(rows)))


def part3():
    print("3. The diagonal argument, finite and exact")
    rng = random.Random(1874)
    # exhaustive adversary: every list of K strings of length K, K <= 4
    for K in range(1, 5):
        strings = list(itertools.product((0, 1), repeat=K))
        n = 0
        for rows in itertools.product(strings, repeat=K):
            assert diagonal(rows) not in rows
            n += 1
        assert n == 2 ** (K * K)
    print("   exhaustive: for K = 1..4 the diagonal is missing from all 2^(K^2) lists"
          " (65536 at K = 4)")
    print("    K    2^K  distinct  missed  gap 2^K-K  bits/point  index bits")
    for K in range(1, 13):
        lists = {
            "random": [tuple(rng.randint(0, 1) for _ in range(K)) for _ in range(K)],
            "identity": [tuple(int(i == j) for j in range(K)) for i in range(K)],
            "constant": [tuple([0] * K)] * K,
            "first K": [tuple(int(b) for b in format(i, f"0{K}b")) for i in range(K)],
        }
        for name, rows in lists.items():
            d = diagonal(rows)
            assert d not in rows
            distinct = len(set(rows))
            missed = 2 ** K - distinct                   # exact, by counting
            all_strings = set(itertools.product((0, 1), repeat=K))
            assert missed == len(all_strings - set(rows))
            assert missed >= 2 ** K - K and d in all_strings - set(rows)
            if name == "random":
                rand_missed, rand_distinct = missed, distinct
        # information reading: 2^K lattice points of [0,1), K bits each; a list of K
        # entries is indexed by log2 K bits and can name at most K of the points
        points, bits, index_bits = 2 ** K, K, math.log2(K)
        gap = points - K
        assert gap == 2 ** K - K and gap > 0
        assert 2 ** bits == points and index_bits <= bits
        print(f"   {K:2d} {points:6d} {rand_distinct:9d} {rand_missed:7d} {gap:10d}"
              f" {bits:11d} {index_bits:11.3f}")
    print("   (distinct / missed: the random list; identity, constant and first-K lists")
    print("   are checked too.)  The list names at most K of the 2^K points; the diagonal")
    print("   is one explicit witness among exactly 2^K - #distinct missed strings.")


def main():
    part1()
    part2()
    part3()
    print("OK 10b_cantor")


if __name__ == "__main__":
    main()

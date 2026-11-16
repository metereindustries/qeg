# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""10b -- Fractal dimension: always defined, and exact at every scale.

Classical problem.  The box-counting dimension of a set F is the limit
lim log N_s(F) / log(1/s) as s -> 0.  The limit need not exist (liminf and
limsup can differ), and in practice it is estimated by a least-squares fit
of log N against log(1/s) on a finite point sample over a chosen "scaling
range".  Different ranges, box families and samples give different numbers.
This is estimator variability, not an error of the classical theory: the
theory defines a limit, and a finite sample does not contain that limit.

Granular resolution (Chapter 12, Fractal Geometry).  A point is a cell of
the lattice of spacing 2eps; lattice point k means k*2eps, and we work with
the integer indices k throughout.  Content is counting, so the box count
N_s at box side s (an integer number of cells) is an exact integer, and the
granular dimension between two scales,
    dim(s, t) = log(N_s / N_t) / log(t / s),
is a definite number at every pair of scales; the classical dimension, when
it exists, is the standard part (shadow) of these numbers.  We check:
  1. Cantor set and Sierpinski carpet on the 3-adic lattice: N(3^j) =
     |D|^(K-j) exactly, so every 3-adic pair of scales gives log|D|/log 3.
  2. By contrast, float least-squares fits on a 50,000-point chaos-game
     sample give range-dependent estimates.
  3. A digit set alternating {0,2} and {0,1,2} in blocks of length 2^k has
     no classical box dimension (liminf != limsup), yet its granular
     dimension at depth K is the exact number (a_K log 2 + c_K log 3)/(K log 3).
  4. Products: N_s(A x B) = N_s(A) N_s(B) exactly, so dimension is additive
     at every scale, not only in the limit.
"""
from fractions import Fraction
import math
import numpy as np


def digit_set(digits_per_level, b):
    """All integers sum_i d_i b^i with d_i in digits_per_level[i] (level 0 = finest)."""
    idx = np.zeros(1, dtype=np.int64)
    for i, D in enumerate(digits_per_level):
        idx = (idx[:, None] + np.array(D, dtype=np.int64)[None, :] * b ** i).ravel()
    return idx


def count1(idx, s):
    """Exact box count of an integer set at box side s (integer floor division)."""
    return len(np.unique(idx // s))


def count2(x, y, s, width):
    """Exact box count of a set of integer pairs at box side s."""
    nb = width // s + 1
    return len(np.unique((x // s) * nb + (y // s)))


def carpet(K):
    """Sierpinski carpet on the 3^K x 3^K lattice: digit pairs != (1, 1)."""
    pairs = [(dx, dy) for dx in range(3) for dy in range(3) if (dx, dy) != (1, 1)]
    x = np.zeros(1, dtype=np.int64)
    y = np.zeros(1, dtype=np.int64)
    for i in range(K):
        dx = np.array([p[0] for p in pairs], dtype=np.int64) * 3 ** i
        dy = np.array([p[1] for p in pairs], dtype=np.int64) * 3 ** i
        x = (x[:, None] + dx[None, :]).ravel()
        y = (y[:, None] + dy[None, :]).ravel()
    return x, y


def part1():
    print("1. Exact box counts on the 3-adic lattice")
    K = 10
    C = digit_set([(0, 2)] * K, 3)
    assert len(C) == 2 ** K and len(np.unique(C)) == 2 ** K
    NC = [count1(C, 3 ** j) for j in range(K + 1)]
    assert NC == [2 ** (K - j) for j in range(K + 1)]
    Kc = 6
    x, y = carpet(Kc)
    assert len(x) == 8 ** Kc
    NS = [count2(x, y, 3 ** j, 3 ** Kc) for j in range(Kc + 1)]
    assert NS == [8 ** (Kc - j) for j in range(Kc + 1)]
    # dimension between any two 3-adic scales: an integer identity, not a fit
    for N, m in ((NC, 2), (NS, 8)):
        for i in range(len(N)):
            for j in range(i + 1, len(N)):
                assert N[i] % N[j] == 0 and N[i] // N[j] == m ** (j - i)
                d = math.log(N[i] // N[j]) / ((j - i) * math.log(3))
                assert abs(d - math.log(m) / math.log(3)) < 1e-12
    print(f"   Cantor, K = {K}:  N(3^j), j = 0..{K}: {NC}")
    print(f"   carpet, K = {Kc}:  N(3^j), j = 0..{Kc}: {NS}")
    print(f"   every pair of scales: Cantor dim = log2/log3 = {math.log(2) / math.log(3):.6f},"
          f" carpet dim = log8/log3 = {math.log(8) / math.log(3):.6f} (exact ratios)")


def part2():
    print("2. Classical regression on a float sample (chaos game, Sierpinski carpet)")
    rng = np.random.default_rng(10)
    n = 50_000
    pairs = np.array([(dx, dy) for dx in range(3) for dy in range(3) if (dx, dy) != (1, 1)],
                     dtype=float)
    pts = np.empty((n, 2))
    z = np.array([0.5, 0.5])
    choice = rng.integers(0, 8, size=n + 100)
    for t in range(n + 100):                     # 100 burn-in steps
        z = (z + pairs[choice[t]]) / 3.0
        if t >= 100:
            pts[t - 100] = z
    target = math.log(8) / math.log(3)

    def counts(sizes):
        return [len(np.unique(np.floor(pts / s).astype(np.int64), axis=0)) for s in sizes]

    def fit(sizes):
        return float(np.polyfit(-np.log(sizes), np.log(counts(sizes)), 1)[0])

    ranges = {                                   # three common, non-3-adic choices
        "decimal, s = 0.2 .. 0.005": np.geomspace(0.2, 0.005, 8),
        "binary, s = 2^-1 .. 2^-5": 2.0 ** -np.arange(1, 6),
        "decimal, s = 0.05 .. 0.002": np.geomspace(0.05, 0.002, 8),
    }
    est = {}
    for name, sizes in ranges.items():
        est[name] = fit(sizes)
        print(f"   {name:28} slope = {est[name]:.4f}   (log8/log3 = {target:.4f})")
    vals = list(est.values())
    spread = max(vals) - min(vals)
    assert spread > 0.1, spread
    assert all(abs(v - target) > 0.01 for v in vals)
    # boxes aligned with the construction recover the exact counts 8^j: the granular count
    s3 = 3.0 ** -np.arange(1, 5)
    assert counts(s3) == [8 ** j for j in range(1, 5)]
    print(f"   (3-adic boxes s = 3^-1 .. 3^-4 on the same sample: counts {counts(s3)} = 8^j,"
          f" slope {fit(s3):.4f})")
    print(f"   spread of the three estimates = {spread:.4f}: estimator variability (range, box")
    print("   family, finite sample), not an error of the classical theory, which defines a limit.")


def alternating_blocks(K):
    """Digit sets per level (coarsest first): block k has length 2^k,
    {0,2} for even k and {0,1,2} for odd k."""
    sets, k = [], 0
    while len(sets) < K:
        sets += [(0, 2) if k % 2 == 0 else (0, 1, 2)] * (2 ** k)
        k += 1
    return sets[:K]


def part3():
    print("3. A set with no classical box dimension, exact granular dimension at every K")
    Kmax = 2 ** 16 - 1
    levels = alternating_blocks(Kmax)
    a = np.cumsum([len(D) == 2 for D in levels])
    c = np.cumsum([len(D) == 3 for D in levels])
    l2, l3 = math.log(2), math.log(3)
    # exact box counts by construction, checked by brute force for small depth
    for K in range(1, 13):
        lv = levels[:K]                                 # coarsest digit first
        idx = digit_set(lv[::-1], 3)                    # digit_set wants finest first
        assert count1(idx, 1) == 2 ** int(a[K - 1]) * 3 ** int(c[K - 1])
        for j in range(K + 1):                          # boxes of side 3^j: drop j finest digits
            aj = sum(len(D) == 2 for D in lv[:K - j])
            cj = sum(len(D) == 3 for D in lv[:K - j])
            assert count1(idx, 3 ** j) == 2 ** aj * 3 ** cj
    # exact dimension at each depth K
    dims = []
    for K in range(1, Kmax + 1):
        aK, cK = int(a[K - 1]), int(c[K - 1])
        assert aK + cK == K
        d = (aK * l2 + cK * l3) / (K * l3)
        if K <= 2000:
            N = 2 ** aK * 3 ** cK                       # exact integer count
            assert abs(math.log(N) / (K * l3) - d) < 1e-12
        dims.append(d)
    # ends of blocks: K = 2^(k+1) - 1
    ends = [(k, 2 ** (k + 1) - 1) for k in range(16)]
    low = [dims[K - 1] for k, K in ends if k % 2 == 0]   # after a {0,2} block
    high = [dims[K - 1] for k, K in ends if k % 2 == 1]  # after a {0,1,2} block
    L_low = (2 / 3) * l2 / l3 + 1 / 3                  # ternary fraction -> 1/3
    L_high = (1 / 3) * l2 / l3 + 2 / 3                 # ternary fraction -> 2/3
    # exact ternary fractions c_K / K at block ends (integers, no limits taken)
    for k, K in ends:
        f = Fraction(int(c[K - 1]), K)
        if k % 2 == 1:
            assert f == Fraction(2, 3)                  # exactly 2/3 after every {0,1,2} block
        else:
            assert f == Fraction(2 ** (k + 1) - 2, 3 * K) < Fraction(1, 3)
    assert all(abs(h - L_high) < 1e-12 for h in high)
    assert all(abs(x - L_low) > abs(y - L_low) for x, y in zip(low, low[1:]))
    assert abs(low[-1] - L_low) < 1e-4
    assert L_high - L_low > 0.1
    assert min(dims[1000:]) < L_low + 1e-3 and max(dims[1000:]) > L_high - 1e-3
    print(f"   N_K = 2^a_K 3^c_K exactly (brute force verified for K <= 12)")
    for k, K in ends[8:]:
        print(f"   K = {K:6d} (end of block {k:2d}, {'{0,2}  ' if k % 2 == 0 else '{0,1,2}'}):"
              f" a = {int(a[K - 1]):6d}, c = {int(c[K - 1]):6d}, dim_K = {dims[K - 1]:.6f}")
    print(f"   liminf -> (2/3)log2/log3 + 1/3 = {L_low:.6f},"
          f" limsup -> (1/3)log2/log3 + 2/3 = {L_high:.6f}")
    print("   c_K/K = 2/3 exactly after every {0,1,2} block, (2^(k+1)-2)/(3K) < 1/3 after {0,2}.")
    print("   classical box dimension does not exist; dim_K is definite at every K.")


def part4():
    print("4. Product additivity at every scale")
    K = 8
    A = digit_set([(0, 2)] * K, 3)
    rng = np.random.default_rng(4)
    B = np.sort(rng.choice(3 ** K, size=500, replace=False)).astype(np.int64)
    X = np.repeat(A, len(B))
    Y = np.tile(B, len(A))
    for s in (1, 2, 3, 5, 7, 9, 27, 100, 243, 1000):
        NA, NB = count1(A, s), count1(B, s)
        NAB = count2(X, Y, s, 3 ** K)
        assert NAB == NA * NB
        print(f"   s = {s:5d}: N(A) = {NA:4d}, N(B) = {NB:4d}, N(AxB) = {NAB:7d} = N(A) N(B)")
    print("   log N(AxB) = log N(A) + log N(B) exactly: dim(AxB) = dim A + dim B at each s.")


def main():
    part1()
    part2()
    part3()
    part4()
    print("OK 10b_fractal_dimension")


if __name__ == "__main__":
    main()

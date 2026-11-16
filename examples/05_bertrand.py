# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""05 -- Bertrand's paradox: three granulations of "a random chord".

Classical problem.  "The probability that a random chord of the unit circle
is longer than sqrt(3)" receives three classical answers, 1/3 (random
endpoints), 1/2 (random distance from the centre), 1/4 (random midpoint).
Each is correct for a different probability on the set of chords; the
phrase "random chord" does not determine one.  The problem is ill-posed.

Granular resolution (Chapter 13: thm:prob-bertrand, ex:prob-bertrand-mid).
A random chord is an outcome of a finite (hyperfinite) space; the three
answers are three different spaces, each computed exactly by counting:
  radial   : distance k/(2M), k < 2M          -> exactly 1/2;
  endpoint : angle 2 pi k/(3M), k < 3M        -> exactly 1/3 - 1/(3M),
             and P(length = sqrt 3) = 2/(3M) > 0;
  midpoint : lattice points of spacing 2eps in the open disc
             -> nu(1/2)/nu(1) = 1/4 + O(eps), centre (a diameter) has P > 0.
All comparisons below are exact integer arithmetic (no square roots).
"""
from fractions import Fraction as F
from math import sqrt
import numpy as np


def radial(M):
    # chord at distance d is longer than sqrt3 iff 4(1 - d^2) > 3
    ds = [F(k, 2 * M) for k in range(2 * M)]
    longer = sum(4 * (1 - d * d) > 3 for d in ds)
    equal = sum(4 * (1 - d * d) == 3 for d in ds)
    return F(longer, 2 * M), F(equal, 2 * M)


def endpoint(M):
    # angle theta = 2 pi k/N; longer iff 2pi/3 < theta < 4pi/3 iff N < 3k < 2N
    N = 3 * M
    return (F(sum(N < 3 * k < 2 * N for k in range(N)), N),
            F(sum(3 * k in (N, 2 * N) for k in range(N)), N))


def endpoint_pairs(M):
    N = 3 * M                              # both endpoints independent and uniform
    hits = sum(N < 3 * ((b - a) % N) < 2 * N for a in range(N) for b in range(N))
    return F(hits, N * N)


def midpoint(n):
    # lattice (Z/n)^2, 2eps = 1/n; midpoint in open disc; longer iff |m| < 1/2
    i = np.arange(-n, n + 1, dtype=np.int64)
    r2 = i[:, None] ** 2 + i[None, :] ** 2
    nu1 = int(np.count_nonzero(r2 < n * n))
    nu_half = int(np.count_nonzero(4 * r2 < n * n))
    return F(nu_half, nu1), nu1


def main():
    print(f"{'M':>5} {'radial':>8} {'endpoint':>18} {'P(=sqrt3), endpt':>17}")
    for M in [1, 2, 5, 10, 100, 1000]:
        pr, pr_eq = radial(M)
        pe, pe_eq = endpoint(M)
        assert pr == F(1, 2) and pr_eq == F(1, 2 * M)                 # (i)
        assert pe == F(1, 3) - F(1, 3 * M) and pe_eq == F(2, 3 * M)   # (ii)
        print(f"{M:5d} {str(pr):>8} {str(pe):>18} {str(pe_eq):>17}")
    for M in [1, 3, 7]:
        assert endpoint_pairs(M) == endpoint(M)[0]       # difference mod N is uniform
    print(f"\n{'n=1/2eps':>8} {'nu(1)':>9} {'P midpoint':>11} {'-1/4':>10} {'bound':>9}")
    for n in [10, 100, 1000, 3000]:
        P, nu1 = midpoint(n)
        e = 1 / (2 * n)                                       # eps
        lo = (0.5 - sqrt(2) * e) ** 2 / (1 + sqrt(2) * e) ** 2
        hi = (0.5 + sqrt(2) * e) ** 2 / (1 - sqrt(2) * e) ** 2
        assert lo <= P <= hi                                    # ex:prob-bertrand-mid
        assert F(1, nu1) > 0                                    # the centre: a diameter
        print(f"{n:8d} {nu1:9d} {float(P):11.7f} {float(P) - 0.25:10.2e} {hi - lo:9.2e}")
    print("Shadows: 1/2, 1/3, 1/4 -- three different spaces, all exact.")
    print("OK 05_bertrand")


if __name__ == "__main__":
    main()

# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""15 -- The Gibbs paradox: configurations are sets, and N! is a theorem.

Classical problem.  With labelled particles in a continuum box, the entropy
of an ideal gas is not extensive: removing a partition between two boxes of
the same gas at the same density raises the entropy by 2N ln 2, although
nothing physical happens.  Classically the fix is to divide the phase-space
volume by N! "by hand" (Gibbs), a correction not derived from the
continuum model, in which a configuration of identical particles has no
canonical description (the volume element of R^{3N} counts orderings).

Granular resolution (Chapter 21: thm:phys-gibbs).  With M cells and N
particles, at most one per cell, a configuration is a set of N cells:
binom(M, N) configurations, and the ordered count is M(M-1)...(M-N+1) =
N! binom(M, N).  Merging two boxes,
    binom(M,N)^2 <= binom(2M, 2N) <= (2N+1) binom(M,N)^2,
so the mixing entropy ln binom(2M,2N) - 2 ln binom(M,N) lies in
[0, ln(2N+1)]: sub-extensive.  Ordered counting gives the spurious 2N ln 2.
All counts are exact integers.
"""
from math import comb, factorial, lgamma, log


def falling(M, N):
    out = 1
    for i in range(N):
        out *= M - i
    return out


def main():
    print(f"{'M':>7} {'N':>5} {'dS/k (sets)':>12} {'ln(2N+1)':>9} {'dS/(N k)':>9} {'ordered':>9}")
    for M, N in [(10, 3), (100, 10), (1000, 100), (10 ** 4, 1000), (10 ** 5, 10 ** 4),
                 (10 ** 6, 10 ** 5)]:
        c, c2 = comb(M, N), comb(2 * M, 2 * N)
        assert falling(M, N) == factorial(N) * c                     # (i): N! is a theorem
        assert c * c <= c2 <= (2 * N + 1) * c * c                    # (ii) exact integers
        dS = log(c2) - 2 * log(c)                                    # math.log takes big ints
        assert 0 <= dS <= log(2 * N + 1) + 1e-9
        # (iii) ordered (labelled) placements without exclusion: (2M)^(2N) vs (M^N)^2
        if N <= 1000:
            assert (2 * M) ** (2 * N) == 2 ** (2 * N) * (M ** N) ** 2
        ordered = 2 * N * log(2)
        print(f"{M:7d} {N:5d} {dS:12.4f} {log(2 * N + 1):9.4f} {dS / N:9.2e} {ordered:9.1f}")
    # dilute limit: binom(M,N) ~ M^N / N!, the Gibbs factor appears as a count
    M, N = 10 ** 9, 50
    ratio = log(comb(M, N)) - (N * log(M) - lgamma(N + 1))
    assert abs(ratio) < N * N / M                                   # ln of prod(1 - i/M)
    print(f"dilute M = 1e9, N = 50: ln binom(M,N) - ln(M^N/N!) = {ratio:.2e}")
    print("OK 15_gibbs_paradox")


if __name__ == "__main__":
    main()

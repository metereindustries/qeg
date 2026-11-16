# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""01 -- Openness information: [a,b], [a,b), (a,b], (a,b).

Classical problem.  Lebesgue measure gives all four intervals with
endpoints a < b the same length b - a and the same first moment
(b^2 - a^2)/2.  "By how much is [0,1] larger than (0,1)?" has no classical
answer: the difference {0, 1} is a null set and the measure algebra of
Lebesgue measure is a quotient in which the four intervals are one element.
The question is not answered wrongly; it has no object.

Granular resolution (Chapter 3: thm:interval-measure,
thm:interval-information, ex:measure-moments).  On the lattice of spacing
2*eps = 1/N the granular measure is a count times 2*eps:
    mu[a,b] = b-a+2eps,  mu[a,b) = mu(a,b] = b-a,  mu(a,b) = b-a-2eps,
and the pair (mu, first moment) determines the interval: the two bits
"left end closed?" and "right end closed?" are retained.  Lebesgue's single
number is the shadow (standard part) of all four granular values.
"""
from fractions import Fraction as F
from math import factorial

KINDS = {"[a,b]": (True, True), "[a,b)": (True, False),
         "(a,b]": (False, True), "(a,b)": (False, False)}


def points(a, b, N, left_closed, right_closed):
    """Lattice points k/N of the interval with lattice endpoints a < b."""
    ka, kb = a * N, b * N
    assert ka.denominator == 1 and kb.denominator == 1, "endpoints must be lattice points"
    lo = int(ka) + (0 if left_closed else 1)
    hi = int(kb) - (0 if right_closed else 1)
    return [F(k, N) for k in range(lo, hi + 1)]


def mu(pts, N):
    return F(len(pts), N)                  # count x (2 eps)


def moment(pts, N):
    return sum(pts, F(0)) / N              # sum of x * (2 eps)


def recover_run(m_val, mom_val, N):
    """thm:interval-information (iv): (mu, moment) -> the run of lattice points."""
    H = m_val * N                          # number of points
    m = (2 * mom_val * N * N / H - H + 1) / 2   # index of the first point
    assert H.denominator == 1 and m.denominator == 1
    return [F(int(m) + i, N) for i in range(int(H))]


def table(a, b, N):
    h = F(1, N)
    print(f"a = {a}, b = {b}, 2eps = 1/{N};  Lebesgue: length {b - a}, "
          f"moment {(b * b - a * a) / 2} for all four")
    print(f"{'I':6} {'#pts':>6} {'(mu-(b-a))/2eps':>16} {'(mom-leb)/eps':>14}  centroid-(a+b)/2")
    seen = set()
    for name, (lc, rc) in KINDS.items():
        pts = points(a, b, N, lc, rc)
        m, mo = mu(pts, N), moment(pts, N)
        closed = lc + rc
        assert m == b - a + (closed - 1) * h          # thm:interval-measure
        assert 1 + (m - (b - a)) / h == closed        # thm:interval-information (i)
        assert recover_run(m, mo, N) == pts           # thm:interval-information (iv)
        seen.add((m, mo))
        dev = (mo - (b * b - a * a) / 2) / (h / 2)
        print(f"{name:6} {len(pts):6d} {str((m - (b - a)) / h):>16} {str(dev):>14}  "
              f"{mo / m - (a + b) / 2}")
    assert len(seen) == 4                             # four distinct granular states
    # thm:interval-information (ii): mom(a,b] - mom[a,b) = (b-a) * 2eps
    assert (moment(points(a, b, N, False, True), N)
            - moment(points(a, b, N, True, False), N)) == (b - a) * h


def main():
    N = factorial(6)                       # N = M!: every 1/q, q <= 6, is a lattice point
    table(F(0), F(1), N)
    # ex:measure-moments: moments 1/2 +- eps for the unit intervals
    eps = F(1, 2 * N)
    expected = {"[a,b]": F(1, 2) + eps, "[a,b)": F(1, 2) - eps,
                "(a,b]": F(1, 2) + eps, "(a,b)": F(1, 2) - eps}
    for name, (lc, rc) in KINDS.items():
        assert moment(points(F(0), F(1), N, lc, rc), N) == expected[name]
    print()
    table(F(1, 3), F(7, 5), N)
    print("\nShadow: |mu[0,1] - mu(0,1)| = 2/N -> 0, the lost two points:")
    for M in range(3, 9):
        N = factorial(M)
        closed, opn = points(F(0), F(1), N, True, True), points(F(0), F(1), N, False, False)
        gap = mu(closed, N) - mu(opn, N)
        assert gap == F(2, N)
        print(f"  N = {M}! = {N:>8}: mu[0,1] - mu(0,1) = {float(gap):.3e}")
    print("OK 01_openness")


if __name__ == "__main__":
    main()

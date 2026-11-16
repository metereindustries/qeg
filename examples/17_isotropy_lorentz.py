# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""17 -- Isotropy and Lorentz invariance at first order in the granule.

Classical problem.  Lebesgue measure is invariant under rotations and under
Lorentz boosts.  The question here is whether the granular content
mu(C) = (2eps)^n #(C cap Lambda) can be invariant at first order in eps.

Granular answer (Chapter 9: prop:geometry-tilted-square,
thm:geometry-polytope-nogo, thm:geometry-smooth-isotropy,
prop:geometry-jittered; Chapter 20: thm:phys-lorentz-retained,
thm:phys-lorentz-nogo; Chapter 3: thm:measure-retained-openness).

* Rotating the unit square by arctan(3/4) changes its content by exactly
  16 eps / 5.  Boosting it with Doppler factor 2 changes it by exactly 3 eps.
* Averaged over all rotations, the unit square loses its whole
  boundary term 4 eps.
* A disc is isotropic at first order on the cubic lattice.
* A jittered set (one random point per cell) is isotropic for squares,
  but no two of its pairs of points share a step.
* The boost orbit of a point is infinite.
* An endpoint off the lattice does not see its openness.
"""
from fractions import Fraction as F
import math
import random


def rot_count(m):
    # index y lies in the rotated unit square at spacing 1/(5m)
    return sum(1 for y1 in range(-3 * m, 4 * m + 1) for y2 in range(0, 7 * m + 1)
               if 0 <= 4 * y1 + 3 * y2 <= 25 * m and 0 <= -3 * y1 + 4 * y2 <= 25 * m)


def boost_count(m):
    # index y lies in the boosted unit square B_2 [0,1]^2 at spacing 1/(4m)
    return sum(1 for y1 in range(0, 8 * m + 1) for y2 in range(0, 8 * m + 1)
               if 0 <= 5 * y1 - 3 * y2 <= 16 * m and 0 <= -3 * y1 + 5 * y2 <= 16 * m)


def count_rotated_square(t, th):
    # lattice points of Z^2 in t * R_th [0,1]^2
    c, s = math.cos(th), math.sin(th)
    n = 0
    lo, hi = int(-2 * t) - 1, int(2 * t) + 2
    for x in range(lo, hi):
        for y in range(lo, hi):
            u, v = c * x + s * y, -s * x + c * y          # R^{-1} (x, y)
            if 0 <= u <= t and 0 <= v <= t:
                n += 1
    return n


def main():
    for m in range(1, 7):
        assert rot_count(m) == 25 * m * m + 2 * m + 1
        assert boost_count(m) == 16 * m * m + 2 * m + 1
        eps = F(1, 10 * m)                                  # 2 eps = 1/(5m)
        d = (2 * eps) ** 2 * ((5 * m + 1) ** 2 - rot_count(m))
        assert d == F(16, 5) * eps
        eps = F(1, 8 * m)                                   # 2 eps = 1/(4m)
        assert (2 * eps) ** 2 * ((4 * m + 1) ** 2 - boost_count(m)) == 3 * eps
    print("rotated square: #=25m^2+2m+1, mu difference = 16 eps/5 exactly (m=1..6)")
    print("boosted square: #=16m^2+2m+1, mu difference = 3 eps exactly (m=1..6)")

    # Haar average over rotations of the unit square: retained term 4 -> about 0
    t = 40
    r = random.Random(17)
    angles = [r.uniform(0, 2 * math.pi) for _ in range(300)]
    avg = sum(count_rotated_square(t, a) for a in angles) / len(angles)
    rho_aligned = ((t + 1) ** 2 - t * t) / (t * t) * (2 * t)      # (mu - 1)/eps, eps = 1/(2t)
    rho_avg = (avg - t * t) / (t * t) * (2 * t)
    assert abs(rho_aligned - 4) < 0.1 and abs(rho_avg) < 1.0
    print(f"unit square, t={t}: retained term aligned {rho_aligned:.3f}, "
          f"rotation average {rho_avg:.3f} (theory 4 and 0)")

    # disc of radius 1/2 centred at (1/2,1/2): rotations change content by o(eps)
    def disc_count(t, th):
        c, s = math.cos(th), math.sin(th)
        cx, cy = t * (c * 0.5 - s * 0.5), t * (s * 0.5 + c * 0.5)
        rr = (t / 2) ** 2
        R = int(t / 2) + 2
        return sum(1 for x in range(int(cx) - R, int(cx) + R + 1)
                   for y in range(int(cy) - R, int(cy) + R + 1)
                   if (x - cx) ** 2 + (y - cy) ** 2 <= rr)
    tt = 400
    devs = [abs(disc_count(tt, a) - math.pi * tt * tt / 4) / (tt * tt) * (2 * tt)
            for a in angles[:40]]
    assert max(devs) < 0.5
    print(f"disc, t={tt}: max over 40 rotations of |mu - area|/eps = {max(devs):.3f} "
          f"(o(1), bound ~ t^(-1/3))")

    # jittered set: one uniform point per cell of the grid of spacing 1/t
    t = 60
    pts = [((i + r.random()) / t, (j + r.random()) / t) for i in range(-2 * t, 2 * t)
           for j in range(-2 * t, 2 * t)]
    worst = 0.0
    for a in angles[:30]:
        c, s = math.cos(a), math.sin(a)
        n = sum(1 for (x, y) in pts if 0 <= c * x + s * y <= 1 and 0 <= -s * x + c * y <= 1)
        worst = max(worst, abs(n - t * t) / (t * t) * (2 * t))
    assert worst < 1.0
    diffs = set()
    sub = pts[:400]
    for i in range(len(sub)):
        for j in range(len(sub)):
            if i != j:
                diffs.add((round(sub[i][0] - sub[j][0], 12), round(sub[i][1] - sub[j][1], 12)))
    assert len(diffs) == len(sub) * (len(sub) - 1)
    print(f"jittered set, t={t}: max over 30 rotations of |mu - 1|/eps = {worst:.3f}; "
          f"no repeated step among {len(sub)} points")

    # boost orbit of a nonzero point is infinite (light-cone coordinates)
    l = F(2)
    p = (F(1), F(0))
    u, v = p[0] + p[1], p[0] - p[1]
    orbit = {(l ** k * u, v / l ** k) for k in range(50)}
    assert len(orbit) == 50 and all(a * b == u * v for a, b in orbit)
    print("boost orbit of (1,0): 50 distinct points on t^2 - x^2 = 1 (never periodic)")

    # openness of an endpoint off the lattice is invisible
    N = 7
    lat = [F(k, N) for k in range(-N, 3 * N)]
    b, c = F(1, 2), F(3, 2)
    closed = sum(1 for x in lat if b <= x <= c)
    open_left = sum(1 for x in lat if b < x <= c)
    assert closed == open_left                     # 1/2 is not on Z/7
    b2 = F(3, 7)
    assert sum(1 for x in lat if b2 <= x <= c) == sum(1 for x in lat if b2 < x <= c) + 1
    print("endpoint 1/2 off Z/7: closed and open counts agree; 3/7 on Z/7: they differ by 1")
    print("OK 17_isotropy_lorentz")


if __name__ == "__main__":
    main()

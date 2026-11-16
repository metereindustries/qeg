# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""12 -- Peano non-uniqueness: x' = sqrt|x|, x(0) = 0.

Classical problem.  The initial value problem has the one-parameter family
of solutions x_c(t) = ((t - c)_+)^2 / 4, c in [0, infinity] (x_inf = 0).
The right-hand side is continuous but not Lipschitz at 0: Peano gives
existence, Picard-Lindelof does not apply, and nothing in the equation
selects a solution.  The problem is ill-posed.

Granular resolution (Chapter 8: thm:ode-sqrt-branches, thm:ode-sqrt-shadow).
The granular equation x_{k+1} = x_k + 2eps sqrt|x_k| has exactly one orbit
from each lattice point.  From the point-sphere at 0 it is identically 0;
from the neighbouring point-sphere 2eps it satisfies, at t = 2 eps k,
    sqrt(2eps) + (t/2)(1 - sqrt(eps/8)) <= sqrt(x(t)) <= sqrt(2eps) + t/2,
so its shadow is t^2/4.  A one-step kick at time t_m gives the shadow
x_c with c = t_m.  Which classical solution one gets is decided by one bit:
is the initial point-sphere the one at 0, or its neighbour?
"""
import math

EPS = 1e-5                                 # granule radius; time step 2 eps


def orbit(x0, steps, kick_at=None):
    x, xs = x0, [x0]
    for k in range(steps):
        if kick_at is not None and k == kick_at:
            x = 2 * EPS                    # move to the neighbouring point-sphere
        x = x + 2 * EPS * math.sqrt(abs(x))
        xs.append(x)
    return xs


def main():
    h = 2 * EPS
    T = 3.0
    n = round(T / h)
    zero = orbit(0.0, n)
    assert all(v == 0.0 for v in zero)                        # (a): exactly 0
    one = orbit(h, n)
    for k in range(0, n + 1, n // 30):                        # sandwich, every sampled t
        t = k * h
        s = math.sqrt(one[k])
        lo = math.sqrt(h) + t / 2 * (1 - math.sqrt(EPS / 8))
        hi = math.sqrt(h) + t / 2
        assert lo - 1e-12 <= s <= hi + 1e-12
    c = 1.0
    kicked = orbit(0.0, n, kick_at=round(c / h))
    print(f"2eps = {h:g}, t in [0, {T}]")
    print(f"{'t':>4} {'from 0':>6} {'from 2eps':>10} {'t^2/4':>7} {'bound':>8} "
          f"{'kick at 1':>10} {'(t-1)_+^2/4':>11}")
    for t in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
        k = round(t / h)
        lo = math.sqrt(h) + t / 2 * (1 - math.sqrt(EPS / 8))
        hi = math.sqrt(h) + t / 2
        bound = max(hi ** 2 - t * t / 4, t * t / 4 - lo ** 2)  # O(sqrt eps), from sandwich
        xc = max(t - c, 0) ** 2 / 4
        assert abs(one[k] - t * t / 4) <= bound < 0.02         # shadow t^2/4
        assert abs(kicked[k] - xc) <= bound                    # shadow x_c (shifted orbit)
        print(f"{t:4.1f} {zero[k]:6.1f} {one[k]:10.6f} {t * t / 4:7.4f} {bound:8.2e} "
              f"{kicked[k]:10.6f} {xc:11.4f}")
    gap = one[n] - zero[n]
    assert gap > 2.0                                           # one lattice step -> macroscopic
    print(f"initial data differ by one point-sphere (2eps = {h:g}); at t = {T}: "
          f"x differs by {gap:.4f}")
    print("OK 12_peano")


if __name__ == "__main__":
    main()

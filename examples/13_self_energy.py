# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""13 -- The self-energy of a point charge: a finite lattice Green's function.

Classical problem.  The Coulomb potential q/(4 pi r) of a point charge is
infinite at the charge and its field energy (1/2) int |E|^2 diverges at
r = 0.  The self-energy of a point charge has no classical value; it needs a
regularisation (smearing radius, cut-off, subtraction), and the answer
depends on the choice.

Granular resolution (Chapter 7: thm:multi-green-origin,
thm:multi-green-single, ex:multi-growing, ex:multi-point-charge,
rem:multi-watson).  On the cubic lattice of spacing 2eps, with
-Lap G = (2eps)^-3 delta, the Green's function at the source is finite on
every region D and increases with D (maximum principle):
    G_{0}(0) = 1/6,  G_{D1}(0) = 1/5,  ...  ->  G_{Z^3}(0) = W/6 = I_3/2
in units of 1/(2eps), with I_3 = 0.50546 Watson's integral and W = 3 I_3.
The self-energy U = q^2 G(0)/2 = (W/24) q^2/eps is finite with no choice
of smearing: the axiom fixed the size of the charge.  Away from the source
G(x) ~ 1/(4 pi |x|), the classical potential as shadow.
(Lattice units 2eps = 1 below.)
"""
from fractions import Fraction as F
from math import gamma, pi, sqrt
import numpy as np


def green_exact(D):
    """Solve 6 G(x) - sum_{nbrs in D} G = [x = 0] exactly on a finite set D."""
    D = sorted(D)
    idx = {p: i for i, p in enumerate(D)}
    A = [[F(0)] * len(D) + [F(int(p == (0, 0, 0)))] for p in D]
    for p, i in idx.items():
        A[i][i] = F(6)
        for d in [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]:
            nb = tuple(a + b for a, b in zip(p, d))
            if nb in idx:
                A[i][idx[nb]] -= 1
    n = len(D)
    for c in range(n):                                   # Gauss-Jordan elimination
        r = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[r] = A[r], A[c]
        A[c] = [v / A[c][c] for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                A[r] = [a - A[r][c] * b for a, b in zip(A[r], A[c])]
    return A[idx[(0, 0, 0)]][-1]


def green_box(n, r=0):
    """Dirichlet box of n^3 sites (n odd), source at the centre; G at centre + r e1."""
    j = np.arange(1, n + 1)
    m = (n + 1) // 2
    th = np.pi * j / (n + 1)
    s0 = 2 / (n + 1) * np.sin(th * m) ** 2
    s1 = 2 / (n + 1) * np.sin(th * m) * np.sin(th * (m + r))
    lam = 2 * (1 - np.cos(th))
    den = lam[:, None, None] + lam[None, :, None] + lam[None, None, :]
    return float((s1[:, None, None] * s0[None, :, None] * s0[None, None, :] / den).sum())


def green_torus(L):
    """Periodic L^3 torus via FFT (neutralising background: zero mode removed)."""
    k = 2 * np.pi * np.fft.fftfreq(L)
    lam = 6 - 2 * (np.cos(k)[:, None, None] + np.cos(k)[None, :, None] + np.cos(k)[None, None, :])
    lam[0, 0, 0] = np.inf
    return np.real(np.fft.ifftn(1 / lam))


def main():
    # Watson's closed form: W = sqrt(6)/(32 pi^3) Gamma(1/24)Gamma(5/24)Gamma(7/24)Gamma(11/24)
    W = sqrt(6) / (32 * pi ** 3) * gamma(1 / 24) * gamma(5 / 24) * gamma(7 / 24) * gamma(11 / 24)
    I3 = W / 3
    assert abs(I3 - 0.50546) < 1e-5 and abs(W / 6 - 0.2527) < 1e-4
    assert abs((1 - 1 / W) - 0.3405) < 1e-4                       # Polya return probability
    D0 = [(0, 0, 0)]
    D1 = D0 + [tuple(s * (i == a) for i in range(3)) for a in range(3) for s in (1, -1)]
    box3 = [(a, b, c) for a in (-1, 0, 1) for b in (-1, 0, 1) for c in (-1, 0, 1)]
    g0, g1, g3 = green_exact(D0), green_exact(D1), green_exact(box3)
    assert g0 == F(1, 6) and g1 == F(1, 5)                        # ex:multi-growing
    assert abs(float(g3) - green_box(3)) < 1e-12
    print(f"Watson: I3 = {I3:.6f}, W = 3 I3 = {W:.6f}, G_Z3(0) = W/6 = {W / 6:.6f}")
    print(f"exact: G_D0(0) = {g0}, G_D1(0) = {g1}, G_3x3x3(0) = {g3} = {float(g3):.6f}")
    print(f"\n{'n (box n^3)':>11} {'G_box(0)':>10} {'W/6 - G':>9}   "
          f"{'L (torus)':>9} {'G_torus(0)':>11}")
    prev = 0.0
    for n, L in [(5, 8), (11, 16), (21, 32), (41, 64), (81, 128), (121, 160)]:
        gb, gt = green_box(n), green_torus(L)[0, 0, 0]
        assert prev < gb < W / 6                                   # monotone, bounded
        prev = gb
        print(f"{n:11d} {gb:10.6f} {W / 6 - gb:9.2e}   {L:9d} {gt:11.6f}")
    assert W / 6 - prev < 3e-3 and abs(W / 6 - gt) < 3e-3
    print(f"\nself-energy U = q^2 G(0)/2 = (W/24) q^2/eps = {W / 24:.4f} q^2/eps (finite)")
    # far field: add back the (nearly constant, harmonic) boundary deficit of the box
    c = W / 6 - green_box(121)
    print(f"{'r':>3} {'G(r e1)':>9} {'1/(4 pi r)':>11} {'ratio':>7}   (box 121^3 + {c:.2e})")
    for r in [0, 1, 2, 4, 8, 16]:
        g = green_box(121, r) + c
        if r == 0:
            print(f"{r:3d} {g:9.6f} {'infinite':>11} {'-':>7}")
            continue
        print(f"{r:3d} {g:9.6f} {1 / (4 * pi * r):11.6f} {g * 4 * pi * r:7.4f}")
        if r == 1:
            assert abs(g - (W / 6 - 1 / 6)) < 1e-4               # 6 G(0) - 6 G(e1) = 1
        if r >= 8:
            assert abs(g * 4 * pi * r - 1) < 0.01                # classical shadow 1/(4 pi r)
    print("OK 13_self_energy")


if __name__ == "__main__":
    main()

# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""04 -- The Borel-Kolmogorov paradox on the granular sphere.

Classical problem.  P uniform on S^2; "the law of P given P in G", G a great
circle, is not defined by Kolmogorov's axioms because P(P in G) = 0.
Conditioning on thin latitude bands gives the uniform law on the equator;
conditioning on thin lunes around a meridian gives latitude density
cos(phi)/2, although equator and meridian are congruent under a rotation
preserving the law of P.  The conditional law given a null event is
ill-posed: it depends on a limiting procedure not contained in the event.

Granular resolution (Chapter 13: sec:prob-borel-kolmogorov, ex:prob-bk,
thm:prob-cond-unif).  In equal-area coordinates (z, longitude) the uniform
law on S^2 is the uniform law on an N_z x L grid (Archimedes).  There are no
null events; each granular event attached to G has positive probability and
an exact conditional law:
  equator row E : longitude uniform on L points (exactly 1/L each);
  lune Lambda   : z uniform on N_z points  -> latitude CDF (1+sin phi)/2;
  tube T_eta    : weights n_j = #{i : r_j |sin lam_i| <= eta}
                  -> latitude uniform on [-pi/2, pi/2] in shadow.
The two classical answers are two different granular events; the datum
Lebesgue measure discards is the width profile of the event along G.
"""
from fractions import Fraction as F
import numpy as np

NZ, L, ETA = 2001, 20000, 0.02            # eps = 1/NZ, cells of probability 1/(NZ L)


def main():
    j = np.arange(NZ)
    z = -1 + (2 * j + 1) / NZ             # cell centres in z (spacing 2 eps)
    r = np.sqrt(1 - z ** 2)
    sin_lam = np.abs(np.sin(2 * np.pi * np.arange(L) / L))
    jstar = (NZ - 1) // 2
    assert z[jstar] == 0.0                 # the equator row

    # (a) equator row: exact uniform conditional law of the longitude
    pE = F(L, NZ * L)
    cond_E = [F(1, NZ * L) / pE] * L
    assert pE == F(1, NZ) and all(c == F(1, L) for c in cond_E)
    # (b) lune = two full columns {i = 0, L/2}: z uniform, exactly 1/NZ
    pLam = F(2 * NZ, NZ * L)
    assert pLam == F(2, L) and F(2, NZ * L) / pLam == F(1, NZ)
    # (c) tube: exact integer weights n_j
    n = np.array([np.count_nonzero(rj * sin_lam <= ETA) for rj in r])
    pT = n.sum() / (NZ * L)

    phis = np.linspace(-1.5, 1.5, 61)
    lune_cdf = np.array([np.count_nonzero(z <= np.sin(p)) / NZ for p in phis])
    tube_cdf = np.array([n[z <= np.sin(p)].sum() / n.sum() for p in phis])
    cos_law = (1 + np.sin(phis)) / 2       # meridian answer, density cos(phi)/2
    unif_law = (phis + np.pi / 2) / np.pi  # rotation-covariant answer
    eps = 1 / NZ
    d = lambda a, b: np.max(np.abs(a - b))
    assert d(lune_cdf, cos_law) <= eps + 1e-12            # ex:prob-bk (b): |theta| <= 1
    assert d(lune_cdf, unif_law) > 0.05
    assert d(tube_cdf, unif_law) < 0.01                    # ex:prob-bk (c), finite eta
    assert d(tube_cdf, cos_law) > 0.05
    assert abs(pT / ETA - 1) < 0.05                        # P(T_eta) ~ eta

    print(f"grid N_z = {NZ}, L = {L}, eta = {ETA}")
    print(f"{'event':10} {'P(event)':>12} {'sup|CDF-cos law|':>18} {'sup|CDF-uniform|':>18}")
    print(f"{'equator E':10} {float(pE):12.3e} {'longitude uniform, exactly 1/L':>37}")
    print(f"{'lune':10} {float(pLam):12.3e} {d(lune_cdf, cos_law):18.2e} "
          f"{d(lune_cdf, unif_law):18.2e}")
    print(f"{'tube':10} {pT:12.3e} {d(tube_cdf, cos_law):18.2e} {d(tube_cdf, unif_law):18.2e}")
    print("phi*      lune  (1+sin)/2   tube  uniform")
    for p in [-1.2, -0.6, 0.0, 0.6, 1.2]:
        k = int(np.argmin(np.abs(phis - p)))
        print(f"{phis[k]:5.2f}  {lune_cdf[k]:7.4f}  {cos_law[k]:8.4f}  "
              f"{tube_cdf[k]:6.4f}  {unif_law[k]:6.4f}")
    print("OK 04_borel_kolmogorov")


if __name__ == "__main__":
    main()

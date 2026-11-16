# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""08 -- Differential entropy: negative, unit-dependent; granular entropy is neither.

Classical problem.  The Shannon entropy of any non-atomic law is infinite,
so continuous information theory uses h(f) = -int f log f, which is not an
information: it depends on the unit of length and can be negative.  For
X ~ N(0, sigma^2), sigma = 1e-3 m: h = -7.9 bits in metres, +2.0 bits in
millimetres.  "How many bits is this measurement?" has no classical answer
(H = infinity, h ill-defined up to log of the unit).

Granular resolution (Chapter 16: thm:entropy-shift, thm:info-shift-shadow,
prop:info-scale, prop:info-negative, ex:info-gauss-table).  At spacing 2eps
(the instrument's resolution) the law is a finite probability vector and
    H = h_eps - log2(2 eps)     exactly,
with h_eps the granular integral of -f log f.  H >= 0 and is the same in
every unit (changing units moves log c between the two summands).  For
sigma = 1e-3 m and 2eps = 1e-6 m: H = 12.0 bits (Ch. 15, Problem 1).
"""
from fractions import Fraction as F
import numpy as np


def lattice_gaussian(sigma, cell, span=12):
    """Normalised lattice sampling p_k = f(k cell) cell / Z on |x| <= span*sigma."""
    k = np.arange(-int(span * sigma / cell), int(span * sigma / cell) + 1)
    f = np.exp(-0.5 * (k * cell / sigma) ** 2) / (sigma * np.sqrt(2 * np.pi))
    Z = f.sum() * cell
    return f / Z, cell                     # granular density, cell volume


def H_bits(f, v):
    p = f * v
    return float(-(p * np.log2(p)).sum())


def h_eps(f, v):                           # granular integral of -f log2 f
    return float(-(f * np.log2(f)).sum() * v)


def main():
    rows = []
    for unit, scale in [("m", 1.0), ("mm", 1e3), ("um", 1e6)]:
        f, v = lattice_gaussian(1e-3 * scale, 1e-6 * scale)
        H, h = H_bits(f, v), h_eps(f, v)
        assert abs(H - (h - np.log2(v))) < 1e-9          # thm:entropy-shift (exact identity)
        assert H >= 0                                    # prop:info-entropy-nonneg
        rows.append((unit, h, -np.log2(v), H))
    print(f"sigma = 1e-3 m, 2eps = 1e-6 m;   H = h_eps - log2(2eps)")
    print(f"{'unit':5} {'h_eps (bits)':>13} {'-log2(2eps)':>12} {'H (bits)':>10}")
    for r in rows:
        print(f"{r[0]:5} {r[1]:13.4f} {r[2]:12.4f} {r[3]:10.4f}")
    Hs = [r[3] for r in rows]
    assert max(Hs) - min(Hs) < 1e-9                      # unit invariant
    assert round(rows[0][1], 1) == -7.9 and round(rows[1][1], 1) == 2.0
    assert round(Hs[0], 1) == 12.0
    assert abs(rows[0][1] - 0.5 * np.log2(2 * np.pi * np.e * 1e-6)) < 1e-9
    # ex:info-gauss-table: sigma = 1, sampling over |x| <= 12
    print(f"\n{'cell':>6} {'H(X_cell)':>10} {'h - log2(cell)':>15} {'difference':>11}")
    hdiff = 0.5 * np.log2(2 * np.pi * np.e)
    book = {2: 0.966747, 1: 2.047095, 0.5: 3.047096, 0.1: 5.369024, 0.01: 8.690952}
    for cell, Hb in book.items():
        f, v = lattice_gaussian(1.0, cell)
        H = H_bits(f, v)
        assert abs(H - Hb) < 5e-7                         # the book's table, 6 decimals
        shift = hdiff - np.log2(cell)
        print(f"{cell:6g} {H:10.6f} {shift:15.6f} {H - shift:11.1e}")
    # prop:info-negative, exactly: uniform on k = 2^10 cells of total length 1/4
    k = 2 ** 10
    v = F(1, 4 * k)
    f = 1 / (k * v)                                       # f = 4
    assert f == 4 and k * v * f == 1
    print(f"\nuniform on {k} cells of total length 1/4: h = -2 bits, "
          f"H = log2 k = {k.bit_length() - 1} bits = -2 - log2(v)")
    assert k.bit_length() - 1 == -2 + (4 * k).bit_length() - 1   # log2 k = -2 - log2 v
    print("OK 08_differential_entropy")


if __name__ == "__main__":
    main()

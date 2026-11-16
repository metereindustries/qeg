# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""Quantisation algebra and quantisability on a fully enumerable toy model.

Chapter 18 (Learning Machines), worked toy example.  Everything is exact
integer arithmetic on lattice indices: a parameter theta = 2*eps*k is stored
as the int8 index k in [-128, 127] with 2*eps = 2**-6.

Toy model: a single attention logit with d_model = d_head = 1,
    z = (x W_Q)(x W_K) = a*b   (x = 1),
with target logit 1 and loss L(a, b) = (a*b - 1)**2.
Solution set S_delta = {L <= delta}, delta = 2**-8, i.e. |k*l - 4096| <= 256.
"""
import math
import numpy as np

SCALE = 64                     # 1/(2 eps): theta = k / 64
LO, HI = -128, 127             # int8 two's complement index range


def qz(r, k):
    """Coarse index of fine index k for ratio r (round half up): (2k+r) // 2r."""
    return (2 * k + r) // (2 * r)


def snap_idx(r, k):
    """Fine index of the snapped point (coarse centre r*qz)."""
    return r * qz(r, k)


def is_solution(k, l):
    """L(k/64, l/64) <= 2**-8  <=>  |k l - 4096| <= 256 (exact, integers)."""
    return abs(k * l - SCALE * SCALE) <= 256


# ---------------------------------------------------------------- algebra
# idempotence of the snap on the fine lattice
for r in (1, 2, 3, 4, 8):
    assert all(snap_idx(r, snap_idx(r, k)) == snap_idx(r, k) for k in range(-512, 512))

# odd ratio nests: ratio r then ratio s (s odd) equals ratio r*s directly
for r in (1, 2, 3, 4):
    for s in (1, 3, 5):
        assert all(qz(s, qz(r, k)) == qz(r * s, k) for k in range(-2000, 2000))

# even ratio: exact double-rounding defect.  Count defects per coarse cell.
def defect_fraction(r, s, span=6144):
    bad = sum(qz(s, qz(r, k)) != qz(r * s, k) for k in range(-span, span))
    return bad / (2 * span)

for r, s in ((2, 2), (4, 2), (2, 4), (3, 2)):
    # predicted: floor(r/2) defective fine points per coarse cell of r*s points,
    # and every defect is exactly one coarse step up
    assert abs(defect_fraction(r, s) - (r // 2) / (r * s)) < 1e-12
    for k in range(-2000, 2000):
        d = qz(s, qz(r, k)) - qz(r * s, k)
        assert d in (0, 1)
print("double-rounding defect fraction, ratios (2,2):", defect_fraction(2, 2))

# carry of a sum: q(a+b) - q(a) - q(b) in {-1, 0, 1} (here in coarse units)
carries = {qz(4, a + b) - qz(4, a) - qz(4, b) for a in range(-64, 64) for b in range(-64, 64)}
assert carries == {-1, 0, 1}

# residuals form a complete residue system: exactly r fine points per coarse cell
for r in (2, 3, 4, 8):
    cells = {}
    for k in range(-10 * r, 10 * r):
        cells.setdefault(qz(r, k), []).append(k - r * qz(r, k))
    inner = [v for c, v in cells.items() if abs(c) < 9]
    assert all(sorted(v) == list(range(-(r // 2), r - r // 2)) for v in inner)

# ---------------------------------------------------------------- the toy model
theta = (93, 44)               # a = 1.453125, b = 0.6875, a*b = 4092/4096
assert is_solution(*theta)
n_sol = sum(is_solution(k, l) for k in range(LO, HI + 1) for l in range(LO, HI + 1))
print("lattice points:", 256 ** 2, " solutions |S_delta| =", n_sol)
assert n_sol == 1434

print(" r | snapped index | success | q_theta(r)")
profile = {}
for J in range(0, 6):
    r = 2 ** J
    sk, sl = snap_idx(r, theta[0]), snap_idx(r, theta[1])
    ok = is_solution(sk, sl)
    qk, ql = qz(r, theta[0]), qz(r, theta[1])
    cell_k = [r * qk + e for e in range(-(r // 2), r - r // 2)]
    cell_l = [r * ql + e for e in range(-(r // 2), r - r // 2)]
    assert all(LO <= k <= HI for k in cell_k + cell_l)
    hits = sum(is_solution(k, l) for k in cell_k for l in cell_l)
    profile[r] = (ok, hits, r * r)
    print("%2d | (%4d,%4d) | %-5s | %4d/%4d = %.4f" % (r, sk, sl, ok, hits, r * r, hits / r ** 2))

assert [profile[2 ** J][0] for J in range(6)] == [True, True, True, False, False, False]
assert [profile[2 ** J][1] for J in range(6)] == [1, 4, 14, 16, 78, 132]
margin = max(J for J in range(6) if all(profile[2 ** i][0] for i in range(J + 1)))
assert margin == 2             # ratio 4: spacing 1/16 survives, ratio 8 fails
print("quantisation margin: J =", margin, "(coarse spacing", 2 ** margin / SCALE, ")")

# ---------------------------------------------------------------- sampling estimate
# q_theta(32) by uniform sampling of the coarse cell; bound P(|qhat-q|>=t) <= 2 exp(-n t^2)
r = 32
q_exact = profile[r][1] / profile[r][2]
t, delta = 0.05, 1e-3
n = math.ceil(math.log(2 / delta) / t ** 2)          # independent of N
rng = np.random.default_rng(15)
qk, ql = qz(r, theta[0]), qz(r, theta[1])
ks = r * qk + rng.integers(-(r // 2), r - r // 2, size=n)
ls = r * ql + rng.integers(-(r // 2), r - r // 2, size=n)
q_hat = np.mean(np.abs(ks * ls - 4096) <= 256)
print("q(32): exact %.4f  sampled %.4f  (n = %d, t = %.2f, delta = %g)" % (q_exact, q_hat, n, t, delta))
assert n == 3041 and abs(q_hat - q_exact) < t

# ---------------------------------------------------------------- single-bit faults
def flip(k, j):
    """Flip bit j of the 8-bit two's-complement pattern of k."""
    u = (k & 0xFF) ^ (1 << j)
    return u - 256 if u >= 128 else u

faults = []
for i in range(2):
    for j in range(8):
        kk = list(theta)
        kk[i] = flip(kk[i], j)
        assert abs(kk[i] - theta[i]) == 2 ** j          # jump is exactly 2^j fine steps
        faults.append((i, j, is_solution(*kk)))
assert len(faults) == 16
survive = [(i, j) for i, j, ok in faults if ok]
print("single-bit faults: 16, tolerated:", survive)
assert survive == [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)]
print("all assertions passed")

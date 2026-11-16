# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""The Walsh--Ito chaos of the Anderson walk and its Wiener--Ito shadow.

Chapter 15 (Stochastic Processes), section "The granular Walsh chaos".

Part A (exact, rational arithmetic on the coin space {+-1}^n):
  * every function F is uniquely sum_S c_S prod_{i in S} xi_i (Walsh expansion),
    with c_S = E[F chi_S]; Parseval;
  * discrete Stroock formula c_S = E[D_S F], D_i F = (F(xi_i=+1)-F(xi_i=-1))/2;
  * number-operator identity sum_S |S| c_S^2 = sum_i E[(D_i F)^2] and the
    Poincare inequality Var F <= sum_i E[(D_i F)^2];
  * W_n(T)^2 = T + 2 tau sum_{i<j} xi_i xi_j exactly.

Part B (shadow, floating point with stated tolerances):
  for g(x1, x2) = cos(c1 x1 + c2 x2 + pi/4) and F_n = g(W_n(t1), W_n(t2)),
  t1, t2 on the time lattice, the discrete kernels f_m^(n)(S) = c_S / tau^(m/2)
  have the closed form
      kappa_m prod_{j not in S} cos(h a_j) prod_{j in S} sin(h a_j)/h,
  h = sqrt(tau), a_j = <c, v_j>, kappa_m = cos(pi/4 + m pi/2), and the
  classical Stroock kernel (ordered-simplex normalisation) is
      phi_m(s) = kappa_m exp(-c.Sigma.c/2) prod_i <c, u(s_i)>.
  The L^2(simplex) distance between the step kernel and phi_m is computed
  exactly (closed form by groups) and its rate is checked: O(tau) for m = 1
  (no diagonal), O(sqrt(tau)) for m = 2 (the diagonal cells), with the
  diagonal constant identified exactly.
"""
import itertools
import math
from fractions import Fraction

import numpy as np


# ------------------------------------------------------------------ Part A
def paths(n):
    return list(itertools.product((1, -1), repeat=n))


def chi(S, w):
    p = 1
    for i in S:
        p *= w[i]
    return p


def subsets(n):
    for m in range(n + 1):
        for S in itertools.combinations(range(n), m):
            yield S


def E(n, X):
    return sum(X(w) for w in paths(n)) / Fraction(2 ** n)


def coeff(n, F, S):
    return E(n, lambda w: F(w) * chi(S, w))


def D(i, F):
    def DF(w):
        wp = list(w); wp[i] = 1
        wm = list(w); wm[i] = -1
        return (F(tuple(wp)) - F(tuple(wm))) / 2
    return DF


n = 5
rng = np.random.default_rng(13)
table = {w: Fraction(int(rng.integers(-9, 10)), int(rng.integers(1, 5))) for w in paths(n)}
F = lambda w: table[w]
G_table = {w: Fraction(int(rng.integers(-9, 10)), 3) for w in paths(n)}
G = lambda w: G_table[w]
cF = {S: coeff(n, F, S) for S in subsets(n)}
cG = {S: coeff(n, G, S) for S in subsets(n)}

# exact expansion
for w in paths(n):
    assert sum(cF[S] * chi(S, w) for S in cF) == F(w)
# uniqueness: the 2^n x 2^n character matrix is invertible (orthogonal up to 2^n)
H = np.array([[chi(S, w) for S in subsets(n)] for w in paths(n)], dtype=np.int64)
assert (H.T @ H == (2 ** n) * np.eye(2 ** n, dtype=np.int64)).all()
# Parseval
assert E(n, lambda w: F(w) * G(w)) == sum(cF[S] * cG[S] for S in cF)
# discrete Stroock formula
for S in subsets(n):
    DSF = F
    for i in S:
        DSF = D(i, DSF)
    assert cF[S] == E(n, DSF)
# number operator and Poincare
energy = sum(E(n, lambda w, i=i: D(i, F)(w) ** 2) for i in range(n))
assert sum(len(S) * cF[S] ** 2 for S in cF) == energy
var = E(n, lambda w: F(w) ** 2) - E(n, F) ** 2
assert var <= energy
# tail bound sum_{|S| >= M} c_S^2 <= energy / M
for M in range(1, n + 1):
    assert sum(cF[S] ** 2 for S in cF if len(S) >= M) <= energy / M

# W_n(T)^2 = T + 2 tau sum_{i<j} xi_i xi_j : c_empty = n tau, c_{ij} = 2 tau
tau = Fraction(1, 7)
W2 = lambda w: tau * sum(w) ** 2
for S in subsets(n):
    c = coeff(n, W2, S)
    expected = n * tau if len(S) == 0 else (2 * tau if len(S) == 2 else 0)
    assert c == expected
print("Part A: Walsh expansion, uniqueness, Parseval, Stroock, number operator,"
      " Poincare, tail bound and W^2 chaos verified exactly (n = %d)" % n)


# ------------------------------------------------------------------ Part B
c1, c2 = 0.7, 0.4
T, t1, t2 = 1.0, 0.25, 0.75          # t1, t2 on the time lattice for n % 4 == 0
Sigma = np.array([[t1, t1], [t1, t2]])
cvec = np.array([c1, c2])
sigma2 = float(cvec @ Sigma @ cvec)
# groups of time cells: [0,t1) -> v=(1,1), [t1,t2) -> (0,1), [t2,T) -> (0,0)
a_groups = [c1 + c2, c2, 0.0]
lengths = [t1, t2 - t1, T - t2]


def kappa(m):
    return math.cos(math.pi / 4 + m * math.pi / 2)


def l2_error_sq(m, nn):
    """Exact ||f~ - phi_m||^2 on the ordered simplex, for m = 1 or 2."""
    tau_ = T / nn
    h = math.sqrt(tau_)
    counts = [round(L / tau_) for L in lengths]
    assert sum(counts) == nn
    base = np.prod([math.cos(h * a) ** k for a, k in zip(a_groups, counts)])
    ratio = [math.sin(h * a) / h / math.cos(h * a) for a in a_groups]   # factor for j in S
    cont = math.exp(-sigma2 / 2)
    err = 0.0
    if m == 1:
        for g in range(3):
            f = kappa(1) * base * ratio[g]
            phi = kappa(1) * cont * a_groups[g]
            err += counts[g] * tau_ * (f - phi) ** 2
        return err
    # m = 2: off-diagonal cells (j1 < j2) with volume tau^2, diagonal cells
    # (j1 = j2, half-cell triangle of volume tau^2/2) where the step kernel is 0
    for g1 in range(3):
        for g2 in range(g1, 3):
            npairs = counts[g1] * (counts[g1] - 1) // 2 if g1 == g2 else counts[g1] * counts[g2]
            f = kappa(2) * base * ratio[g1] * ratio[g2]
            phi = kappa(2) * cont * a_groups[g1] * a_groups[g2]
            err += npairs * tau_ ** 2 * (f - phi) ** 2
    for g in range(3):
        phi = kappa(2) * cont * a_groups[g] ** 2
        err += counts[g] * tau_ ** 2 / 2 * phi ** 2
    return err


# check the closed-form kernel against brute-force Walsh coefficients (n = 8)
nb = 8
tau_b = T / nb
hb = math.sqrt(tau_b)
k1, k2 = round(t1 / tau_b), round(t2 / tau_b)
a_of = [c1 * (j < k1) + c2 * (j < k2) for j in range(nb)]
allw = np.array(paths(nb), dtype=float)
W1 = hb * allw[:, :k1].sum(axis=1)
W2b = hb * allw[:, :k2].sum(axis=1)
Fvals = np.cos(c1 * W1 + c2 * W2b + math.pi / 4)
for S in subsets(nb):
    cS = float(np.mean(Fvals * np.prod(allw[:, list(S)], axis=1))) if S else float(np.mean(Fvals))
    m = len(S)
    closed = kappa(m) * np.prod([math.cos(hb * a_of[j]) for j in range(nb) if j not in S]) \
        * np.prod([math.sin(hb * a_of[j]) / hb for j in S]) * hb ** m
    assert abs(cS - closed) < 1e-12
print("Part B: closed-form discrete kernels agree with brute-force Walsh coefficients (n = 8)")

ns = [64, 256, 1024, 4096, 16384]
e1 = [math.sqrt(l2_error_sq(1, k)) for k in ns]
e2 = [math.sqrt(l2_error_sq(2, k)) for k in ns]
for a, b in zip(e1, e1[1:]):
    assert 3.5 < a / b < 4.5, (a, b)          # O(tau): ratio 4 per factor 4 in n
for a, b in zip(e2, e2[1:]):
    assert 1.9 < a / b < 2.1, (a, b)          # O(sqrt tau): ratio 2
# the m = 2 error is dominated by the diagonal: e2^2 / tau -> (1/2) sum_g L_g phi_gg^2
diag_const = 0.5 * sum(L * (kappa(2) * math.exp(-sigma2 / 2) * a ** 2) ** 2
                       for L, a in zip(lengths, a_groups))
assert abs(e2[-1] ** 2 / (T / ns[-1]) / diag_const - 1) < 2e-3
print("Part B: kernel L2 errors, m=1:", ["%.3e" % x for x in e1])
print("        kernel L2 errors, m=2:", ["%.3e" % x for x in e2])
print("        m=1 rate O(tau); m=2 rate O(sqrt(tau)), diagonal constant %.6f" % diag_const)

# sharpness: F = W(T)^2, Gaussian lift minus Wiener chaos = -sum_j (Delta B_j^2 - tau);
# its L2 norm is sqrt(n * Var(G^2)) * tau = sqrt(2 T tau) exactly (E G^4 = 3)
for k in ns:
    tau_ = T / k
    lhs = math.sqrt(k * (3 - 1) * tau_ ** 2)
    assert abs(lhs - math.sqrt(2 * T * tau_)) < 1e-15
print("Sharpness: ||Pi_2 lift - Pi_2 F||_2 = sqrt(2 T tau) for F = W(T)^2")

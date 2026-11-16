# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""18 -- Granular Pesin formula, granular H-theorem, limit cycles of training.

Classical problems.  (i) Pesin's formula h_KS = sum of positive Lyapunov
exponents is a statement about t -> infinity; at finite resolution the
entropy of the join must saturate, and classically there is no object that
says when.  (ii) Boltzmann's H-theorem against Loschmidt's reversal: the
classical answer appeals to typicality, not to a count.  (iii) Rounded
gradient descent can cycle; classically there is no limit cycle at all.

Granular resolution (Chapter 17: thm:dyn-pesin, thm:dyn-htheorem,
thm:dyn-boltzmann; Chapter 18: thm:learning-period-two).
* Cat map with the q x q grid partition on (Z/N)^2:
  log(N^2/(2 rho + 1)^2) <= H_t <= 2 log N exactly, and numerically
  H_t = min(2 log q + (t-1) log lambda, 2 log N) + O(1): the Lyapunov rate
  up to the saturation time t_sat = 2 log N / log lambda, then the budget.
* Reversible dynamics: #{S decreases by >= Delta} = #{S increases by >= Delta}
  exactly, every t; Boltzmann: fraction decreasing by >= Delta <= K e^-Delta.
* Rounded descent theta -> round(L theta + b), L symmetric: periods 1 or 2
  only (Goles-Olivos type energy); seeded SGD: period = multiple of the PRNG
  period.
"""
import math
import random
from itertools import product

import numpy as np

PHI = (1 + 5 ** 0.5) / 2
LAM = PHI ** 2


# ------------------------------------------------------------- Pesin
def join_entropies(N, q, T):
    """Shannon entropies (nats) of the t-step joins of the q x q grid, t = 1..T."""
    W = N // q
    x, y = np.meshgrid(np.arange(N), np.arange(N))
    x, y = x.ravel().astype(np.int64), y.ravel().astype(np.int64)
    lab = np.zeros(N * N, np.int64)
    out = []
    for _ in range(T):
        _, lab = np.unique(lab * (q * q) + (x // W) * q + (y // W), return_inverse=True)
        cnt = np.bincount(lab)
        p = cnt / (N * N)
        out.append(float(-(p * np.log(p)).sum()))
        x, y = (2 * x + y) % N, (x + y) % N
    return out


def lean_lower(N, q, t):
    R = N // q - 1
    best = -1e9
    for m in range(0, t + 1):
        rho = PHI ** 2 * R * (PHI ** (2 * m) / PHI ** (2 * (t - 1)) + 1 / PHI ** (2 * m))
        best = max(best, math.log(N ** 2 / (2 * rho + 1) ** 2))
    return best


def check_pesin():
    print("granular Pesin formula, cat map, q x q grid partition (nats):")
    for N, q in [(256, 8), (1024, 8)]:
        print(f"  N = {N}, q = {q}: t_sat = 2 ln N / ln lambda = {2 * math.log(N) / math.log(LAM):.1f}")
        print(f"  {'t':>3} {'H_t':>8} {'min(2ln q+(t-1)ln lam, 2ln N)':>30} {'Lean lower':>11}")
        devs = []
        Hs = join_entropies(N, q, 15)
        for t in range(1, 16):
            H = Hs[t - 1]
            prof = min(2 * math.log(q) + (t - 1) * math.log(LAM), 2 * math.log(N))
            lo = lean_lower(N, q, t)
            assert lo <= H + 1e-9 and H <= 2 * math.log(N) + 1e-9     # thm:dyn-pesin
            devs.append(H - prof)
            print(f"  {t:3d} {H:8.3f} {prof:30.3f} {lo:11.3f}")
        assert max(abs(d) for d in devs) < 1.2
        # closed forms of thm:dyn-pesin / cor:dyn-pesin-profile
        W = N // q
        for t in range(1, 16):
            H = Hs[t - 1]
            lo = 2 * math.log(N) - 2 * math.log(1 + 2 * PHI ** 4 * (W - 1) / PHI ** (t - 1))
            lo2 = min((t - 1) * math.log(LAM) + 2 * math.log(q) - 7, 2 * math.log(N) - 2 * math.log(2))
            assert lo2 <= lo + 1e-9 and lo <= H + 1e-9
            for L in [1, 2, 4, 8, 16]:
                m = t // 2
                S = PHI ** 2 * (L - 1) * (t + (LAM ** (m + 1) + LAM ** (t - m)) / (LAM - 1)) + t
                up = 2 * math.log(N / L) + 8 * q * math.log(q) / N * S
                assert H <= up + 1e-9
        # increments h_eps(t) -> ln lambda before saturation
        H5, H8 = Hs[4], Hs[7]
        if N == 1024:
            assert abs((H8 - H5) / 3 - math.log(LAM)) < 0.1


# -------------------------------------------------------- H-theorem
def check_htheorem():
    N, n, m = 9, 3, 3                    # 3 particles on Z/9, 3 spatial cells
    F = lambda q: (2 * q * q + 1) % N    # an arbitrary nonlinear force
    states = list(product(range(N), repeat=2 * n))     # (q1..qn, p1..pn)
    idx = {s: i for i, s in enumerate(states)}

    def lam(s):
        q, p = s[:n], s[n:]
        p1 = tuple((p[i] + F(q[i])) % N for i in range(n))
        q1 = tuple((q[i] + p1[i]) % N for i in range(n))
        return q1 + p1

    cell = lambda a: a * m // N
    occ = lambda s: tuple(sum(1 for i in range(n) if cell(s[i]) == c) for c in range(m))
    from collections import Counter
    size = Counter(occ(s) for s in states)
    S = lambda s: math.log(size[occ(s)])
    f = np.array([idx[lam(s)] for s in states])
    Sv = np.array([S(s) for s in states])
    K = len(size)
    assert K <= (n + 1) ** m
    g = np.arange(len(states))
    for t in range(1, 5):
        g = f[g]
        for D in [0.0, 0.5, 1.0, 2.0]:
            dec = int(np.sum(Sv[g] + D <= Sv - 1e-12)) if D == 0 else int(np.sum(Sv[g] + D <= Sv + 1e-12))
            inc = int(np.sum(Sv + D <= Sv[g] - 1e-12)) if D == 0 else int(np.sum(Sv + D <= Sv[g] + 1e-12))
            assert dec == inc                                   # thm:dyn-htheorem
            assert dec <= K * math.exp(-D) * len(states) + 1e-9  # thm:dyn-boltzmann
    print(f"\ngranular H-theorem: {n} particles on (Z/{N})^2, {m} cells, {len(states)} microstates, "
          f"{K} macrostates: #decrease = #increase for every t <= 4 and Delta; "
          f"Boltzmann bound K e^-Delta holds")


# --------------------------------------------------------- training
def rdesc(L, b, th):
    v = L @ th + b
    return np.floor(v + 0.5).astype(np.int64)


def cycle_len(G, th, maxit=10000):
    seen = {}
    for t in range(maxit):
        k = tuple(th)
        if k in seen:
            return t - seen[k]
        seen[k] = t
        th = G(th)
    return None


def check_training():
    rnd = np.random.default_rng(3)
    periods = set()
    for _ in range(150):
        A = rnd.normal(size=(3, 3))
        H = A @ A.T + 0.1 * np.eye(3)                        # SPD Hessian
        eta = rnd.uniform(0.2, 1.99) / np.linalg.eigvalsh(H).max()
        L = np.eye(3) - eta * H                              # symmetric
        b = rnd.normal(size=3) * 0.3
        G = lambda th: rdesc(L, b, th)
        for _ in range(20):
            th = rnd.integers(-30, 31, size=3)
            P = cycle_len(G, th)
            if P is not None:
                periods.add(P)
                assert P <= 2                                  # thm:learning-period-two
    # symmetry is needed: a non-symmetric contraction with a 3-cycle (found by search)
    nonsym = None
    for a, bb, c, d in product(range(-9, 10), repeat=4):
        L = np.array([[a, bb], [c, d]]) / 10
        if bb == c or abs(a) + abs(bb) >= 10 or abs(c) + abs(d) >= 10:
            continue
        for th0 in product(range(-4, 5), repeat=2):
            P = cycle_len(lambda th: rdesc(L, np.zeros(2), th), np.array(th0), 50)
            if P is not None and P >= 3:
                nonsym = (L, th0, P)
                break
        if nonsym:
            break
    assert nonsym is not None
    # cyclic mini-batches: two symmetric convex steps with a 4-cycle (thm:learning-period-two(d))
    L1, L2 = np.array([[-0.9, 0.4], [0.4, 0.9]]), np.array([[0.0, 0.6], [0.6, 0.0]])
    assert min(np.linalg.eigvalsh(np.eye(2) - L1)) > 0 and min(np.linalg.eigvalsh(np.eye(2) - L2)) > 0
    C = lambda th: rdesc(L2, np.zeros(2), rdesc(L1, np.zeros(2), th))
    assert cycle_len(C, np.array([0, 1])) == 4
    # seeded SGD: the training period is a multiple of the PRNG period
    mod, a, c = 2 ** 8, 5, 3                                   # full-period LCG, period 256
    Ls = [np.array([[0.5, 0.2], [0.2, 0.6]]), np.array([[0.7, -0.1], [-0.1, 0.4]])]
    s, th = 1, np.array([7, -5])
    seen = {}
    for t in range(200000):
        key = (tuple(th), s)
        if key in seen:
            P = t - seen[key]
            break
        seen[key] = t
        th = rdesc(Ls[s & 1], np.array([0.3, -0.2]), th)
        s = (a * s + c) % mod
    assert P % 256 == 0
    print(f"\nrounded descent, 150 random symmetric 3x3 quadratics: periods {sorted(periods)} "
          f"(<= 2); non-symmetric L = {nonsym[0].tolist()} has a {nonsym[2]}-cycle; "
          f"seeded SGD period {P} = multiple of the PRNG period 256")


def main():
    check_pesin()
    check_htheorem()
    check_training()
    print("OK 18_pesin_htheorem")


if __name__ == "__main__":
    main()

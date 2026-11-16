# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""17 -- Periods of granular chaotic maps: chaos as overflow.

Classical problem.  A chaotic map iterated on a computer is a self-map of a
finite set, hence eventually periodic.  How long are the periods?  The
classical heuristic (Grebogi-Ott-Yorke 1988; Flajolet-Odlyzko 1990) treats
the discretised map as a random mapping, period ~ sqrt(pi M / 8), and a
discretised invertible map as a random permutation, period ~ M^2; neither is
a theorem for any explicit map.

Granular resolution (Chapter 17, sec:dyn-overflow and sec:dyn-periods).
* Circular granulation: the logistic map l_4 is the doubling map in the
  coordinate x = sin^2(pi theta); on the M-cell circle it is k -> 2k mod M,
  one bit of overflow per step, with EXACT periods: for M = 2^a m, m odd,
  the preperiod is <= a and the period of k is ord(2 mod m/gcd(k,m))
  (thm:dyn-circular); on the logistic nodes the period is the order of 2
  in (Z/d)^*/{+-1}.  These orders are typically much larger than sqrt(M)
  (Kurlberg-Pomerance 2005).
* The x-rounded logistic map overflows twice: at the fold one rounding
  erases a theta-interval of width ~ sqrt(2h)/pi (thm:dyn-xround); its
  orbits leave the true orbit after about half the circular horizon.
* Cat map mod a prime p != 2, 5: c^((p-1)/2) = id or c^(p+1) = id
  (thm:dyn-cat-prime): periods <= p + 1, not ~ p^2.
* Kick-drift maps are reversible: at least N/2 symmetric cycles on (Z/N)^2,
  N odd (thm:dyn-symmetric-cycles), against ~ 2 ln N cycles for a random
  permutation.
* Granular period doubling: every cycle of the snapped logistic map on M+1
  points has length <= M/2 + 1 (thm:dyn-cascade); n_* grows like
  log(1/eps), and the lattice thresholds show Feigenbaum's delta.
* Channel capacity of the state: the closed lattice of [0,1] has M+1 points,
  capacity log2(M+1) bits; a symmetric step f(M-k) = f(k) (the fold of the
  logistic map) has image <= (M+1)/2 for odd M, so it loses >= 1 bit
  (thm:dyn-fold-bit); the circular doubling with M = 2^a m overflows exactly
  min(t, a) bits in t steps (thm:dyn-circ-overflow).
"""
import math
import random
from fractions import Fraction  # noqa: F401  (exact arithmetic is done with integers)

import numpy as np


# ---------------------------------------------------------------- circle
def mult_order(b, d):
    """Multiplicative order of b modulo d (d >= 1, gcd(b, d) = 1)."""
    if d == 1:
        return 1
    x, n = b % d, 1
    while x != 1:
        x, n = x * b % d, n + 1
    return n


def pm_order(b, d):
    """Least n >= 1 with b^n = +-1 (mod d)."""
    if d <= 2:
        return 1
    x, n = b % d, 1
    while x != 1 and x != d - 1:
        x, n = x * b % d, n + 1
    return n


def split2(M):
    a = 0
    while M % 2 == 0:
        M, a = M // 2, a + 1
    return a, M


def orbit_pre_per(f, x):
    seen, t = {}, 0
    while x not in seen:
        seen[x] = t
        x, t = f(x), t + 1
    return seen[x], t - seen[x]


def check_circle():
    for M in [999, 1000, 1001, 1024, 3 * 2 ** 5 * 7, 2 ** 4 * 45, 2 ** 3 * 125]:
        a, m = split2(M)
        for k in range(M):
            pre, per = orbit_pre_per(lambda j: 2 * j % M, k)
            assert pre <= a                                     # preperiod <= a
            d = m // math.gcd(k, m)
            assert per == mult_order(2, d), (M, k)              # thm:dyn-circular
    # the logistic map is exact on the circular nodes, with +-1 periods
    M = 1001
    node = lambda k: math.sin(math.pi * k / M) ** 2
    for k in range(M):
        x = node(k)
        assert abs(4 * x * (1 - x) - node(2 * k % M)) < 1e-12
    for k in range(M):
        pre, per = orbit_pre_per(lambda j: min(2 * j % M, M - 2 * j % M), min(k, M - k))
        d = M // math.gcd(k, M)
        assert per == pm_order(2, d)
    print("circular granulation: preperiod <= a, period = ord(2 mod m/gcd(k,m)) for all k; "
          "logistic nodes exact, period = ord of 2 in (Z/d)^*/{+-1}")
    # typical size of the circular period ord*(2, M) (the period of k = 1)
    X = 20000
    big = sum(1 for M in range(3, X) if mult_order(2, split2(M)[1]) >= math.sqrt(M))
    frac = big / (X - 3)
    print(f"  fraction of M < {X} with ord*(2,M) >= sqrt(M): {frac:.3f}")
    assert frac > 0.85


# ------------------------------------------------------- x-rounded logistic
def functional_graph_periods(f):
    """Period of the cycle reached from each start, for an integer map f (numpy)."""
    n = len(f)
    S = np.unique(f)
    while True:
        S2 = np.unique(f[S])
        if len(S2) == len(S):
            break
        S = S2
    cid = -np.ones(n, np.int64)
    lens = []
    for s in S:
        if cid[s] >= 0:
            continue
        cyc, x = [s], f[s]
        while x != s:
            cyc.append(x)
            x = f[x]
        cid[cyc] = len(lens)
        lens.append(len(cyc))
    lab = cid.copy()
    while (lab < 0).any():
        msk = lab < 0
        lab[msk] = lab[f[msk]]
    return np.array(lens)[lab], np.array(lens)


def check_xrounded():
    ratios = []
    print(f"\n  {'M':>8} {'E[period]':>10} {'sqrt(pi M/8)':>13} {'ratio':>7} {'P(->0)':>7}")
    for K in range(10, 21, 2):
        D = 2 ** K
        k = np.arange(D + 1, dtype=np.int64)
        f = (8 * k * (D - k) + D) // (2 * D)                  # round(4 k (D - k) / D)
        per, lens = functional_graph_periods(f)
        assert lens.max() <= D // 2 + 1                         # thm:dyn-cascade bound
        E = per.mean()
        r = E / math.sqrt(math.pi * (D + 1) / 8)
        ratios.append(r)
        print(f"  {D + 1:8d} {E:10.1f} {math.sqrt(math.pi * (D + 1) / 8):13.1f} {r:7.3f} "
              f"{(per == 1).mean():7.3f}")
    assert max(ratios) / min(ratios) > 5        # no clean random-mapping law at these sizes
    print("  x-rounded logistic: periods erratic in M (ratio to sqrt(pi M/8) varies by "
          f"{max(ratios) / min(ratios):.0f}x); 0 is absorbing")


def check_horizons():
    """Divergence from the true orbit: circular vs x-rounded granulation."""
    rnd = random.Random(7)
    M = 2 ** 20 + 1                              # odd: the circular map is a permutation
    B = 200                                      # true theta has 200 exact bits
    two_B = 1 << B

    def true_x(n, t):
        return math.sin(math.pi * ((n << t) % two_B) / two_B) ** 2

    def horizon_circ(n):
        j = round(n * M / two_B) % M
        for t in range(120):
            if abs(math.sin(math.pi * j / M) ** 2 - true_x(n, t)) > 0.1:
                return t
            j = 2 * j % M
        return 120

    def horizon_x(n):
        k = round(true_x(n, 0) * M)
        for t in range(120):
            if abs(k / M - true_x(n, t)) > 0.1:
                return t
            k = (8 * k * (M - k) + M) // (2 * M)
        return 120

    bulk_c, bulk_x, bd_c, bd_x = [], [], [], []
    for _ in range(300):
        n = rnd.randrange(1, two_B)
        bulk_c.append(horizon_circ(n))
        bulk_x.append(horizon_x(n))
        # boundary region: |theta| < sqrt(h)/pi, the fold of x = sin^2(pi theta)
        n = rnd.randrange(1, int(two_B / (math.pi * math.sqrt(M))))
        bd_c.append(horizon_circ(n))
        bd_x.append(horizon_x(n))
    mc, mx, bc, bx = map(np.mean, (bulk_c, bulk_x, bd_c, bd_x))
    print(f"\n  horizons (steps, M = 2^20+1, log2 M = {math.log2(M):.1f}):")
    print(f"    bulk start:     circular {mc:5.2f}   x-rounded {mx:5.2f}")
    print(f"    boundary start: circular {bc:5.2f}   x-rounded {bx:5.2f}   ratio {bx / bc:.2f}")
    assert abs(mx - mc) < 1.5 and bx < bc        # equal in the bulk, worse at the fold
    assert 0.35 <= bx / bc <= 0.65              # thm:dyn-xround: half the horizon
    assert abs(bc - math.log2(M)) < 4


# ------------------------------------------------------------------ cat map
def cat_period(N):
    a, b, c, d, n = 2 % N, 1 % N, 1 % N, 1 % N, 1
    while (a, b, c, d) != (1 % N, 0, 0, 1 % N):
        a, b, c, d = (2 * a + c) % N, (2 * b + d) % N, (a + c) % N, (b + d) % N
        n += 1
    return n


def primes(n):
    s = bytearray([1]) * (n + 1)
    s[:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def check_cat():
    for p in primes(3000):
        if p in (2, 5):
            continue
        P = cat_period(p)
        assert ((p - 1) // 2) % P == 0 or (p + 1) % P == 0     # thm:dyn-cat-prime
        assert P <= p + 1
    for N in range(2, 400):
        assert N <= fib(2 * cat_period(N))                     # Pi(N) >= log_lambda N
    # most states have the full period
    for p in [101, 103, 107, 109, 113]:
        P = cat_period(p)
        x, y = np.meshgrid(np.arange(p), np.arange(p))
        x, y = x.ravel(), y.ravel()
        x0, y0 = x.copy(), y.copy()
        per = np.zeros(p * p, np.int64)
        for t in range(1, P + 1):
            x, y = (2 * x + y) % p, (x + y) % p
            back = (x == x0) & (y == y0) & (per == 0)
            per[back] = t
        nfac = len([q for q in primes(P) if P % q == 0])
        assert (per == P).mean() >= 1 - nfac / p
    print("\ncat map mod p (p < 3000, p != 2, 5): Pi(p) | (p-1)/2 or Pi(p) | p+1, so "
          "every period <= p+1; N <= F_{2 Pi(N)}; most states have period Pi(p)")


# ------------------------------------------------------- reversible maps
def check_reversible():
    rows = []
    for N in [101, 151, 201, 251]:
        kap = 1.5
        F = np.array([round(kap * N / (2 * math.pi) * math.sin(2 * math.pi * q / N))
                      for q in range(N)], np.int64)
        q, p = np.meshgrid(np.arange(N), np.arange(N), indexing="ij")
        q, p = q.ravel(), p.ravel()
        idx = lambda a, b: a * N + b
        p1 = (p + F[q]) % N
        q1 = (q + p1) % N
        lam = idx(q1, p1)
        per, lens = functional_graph_periods(lam)
        ncyc = len(lens)
        # symmetric cycles: those through Fix(rho) or Fix(rho Lambda)
        inv2 = pow(2, -1, N)
        fixG = [idx(a, (-F[a] * inv2) % N) for a in range(N)]
        fixH = [idx(a, (-F[a]) % N) for a in range(N)]
        # identify cycles
        cyc_of = -np.ones(N * N, np.int64)
        c = 0
        for s in range(N * N):
            if cyc_of[s] >= 0:
                continue
            x = s
            while cyc_of[x] < 0:
                cyc_of[x] = c
                x = lam[x]
            c += 1
        sym = len(set(cyc_of[fixG]) | set(cyc_of[fixH]))
        assert 2 * len(set(cyc_of[fixG])) >= N                  # thm:dyn-symmetric-cycles
        assert sym == N                                         # exact count (remark)
        H = sum(1 / k for k in range(1, N * N + 1))
        rows.append((N, ncyc, sym, H, per.mean() / N))
    print("\nkick-drift standard map on (Z/N)^2 (reversible):")
    print(f"  {'N':>5} {'#cycles':>8} {'#symmetric':>11} {'random perm E#':>15} {'E[period]/N':>12}")
    for N, ncyc, sym, H, r in rows:
        print(f"  {N:5d} {ncyc:8d} {sym:11d} {H:15.1f} {r:12.2f}")
        assert ncyc >= N / 2 > 3 * H
        assert 0.5 < r < 4          # periods of order N (Roberts-Vivaldi), not N^2


# --------------------------------------------------------- the cascade
RINF = 3.5699456718709449


def period_from_half(r, M):
    k, seen, t = M // 2, {}, 0
    while k not in seen:
        seen[k] = t
        t += 1
        k = min(M, int(math.floor(r * k * (M - k) / M + 0.5)))
    return t - seen[k]


def check_cascade():
    print("\ngranular period-doubling cascade of the snapped logistic map:")
    nst = {}
    for K in [12, 16, 20, 24, 28]:
        M = 2 ** K
        first = {}
        for dd in np.exp(np.linspace(0.0, math.log(1e-11), 4000)):
            r = RINF - dd
            P = period_from_half(r, M)
            assert P <= M // 2 + 1                       # thm:dyn-cascade
            if P & (P - 1) == 0 and P not in first:
                first[P] = r
        n = int(math.log2(max(first)))
        nst[K] = n
        assert 2 ** n <= M // 2 + 1
        thr = [first[2 ** j] for j in range(3, n + 1) if 2 ** j in first]
        dl = [(thr[i + 1] - thr[i]) / (thr[i + 2] - thr[i + 1]) for i in range(len(thr) - 2)]
        print(f"  K = {K:2d} (M = 2^K): n_* = {n:2d}, n_*/K = {n / K:.2f}, "
              f"delta estimates {', '.join(f'{d:.2f}' for d in dl[:6])}")
        if K == 28:
            assert 4.0 < float(np.median(dl)) < 5.4
    ks = sorted(nst)
    assert all(nst[a] <= nst[b] for a, b in zip(ks, ks[1:]))
    assert all(0.3 <= nst[K] / K <= 0.5 for K in ks if K >= 16)
    # monotone/antitone structure: mu > 0 gives exactly period 2, mu < 0 allows 4
    M = 2 ** 20
    assert period_from_half(3.15, M) == 2          # 2-cycle with multiplier in (0, 1)
    assert period_from_half(3.30, M) in (2, 4)     # multiplier in (-1, 0): 2 or 4
    print("  every cycle <= M/2 + 1; n_* ~ 0.4 log2 M; mu>0 -> period exactly P, "
          "mu<0 -> P or 2P")


# ------------------------------------------------- channel capacity of the state
def check_capacity():
    """log2(M + 1) is the channel capacity of the closed-interval state."""
    snap = lambda r, M, k: min(M, int(math.floor(r * k * (M - k) / M + 0.5)))
    for M in [1, 3, 7, 101, 1001, 1023]:                     # odd M: no fixed point of k -> M - k
        assert all(M - k != k for k in range(M + 1))
        for r in [0.5, 2.5, 3.2, 3.5, 3.83, 4.0]:
            img = {snap(r, M, k) for k in range(M + 1)}
            assert all(snap(r, M, M - k) == snap(r, M, k) for k in range(M + 1))
            assert 2 * len(img) <= M + 1                       # thm:dyn-fold-bit, odd M
            assert math.log2(M + 1) - math.log2(len(img)) >= 1 - 1e-12
            S = set(range(M + 1))                              # t-step images are nested
            prev = len(S)
            for _ in range(6):
                S = {snap(r, M, k) for k in S}
                assert len(S) <= prev and 2 * len(S) <= M + 1
                prev = len(S)
    for M in [2, 100, 1000, 1024]:                             # even M: loss >= log2(2(M+1)/(M+2))
        for r in [2.5, 3.5, 4.0]:
            img = {snap(r, M, k) for k in range(M + 1)}
            assert len(img) <= M // 2 + 1
            assert math.log2(M + 1) - math.log2(len(img)) >= math.log2(2 * (M + 1) / (M + 2)) - 1e-12
    # the second fold need not cost another bit: at r = 4, M = 101 two steps lose < 2 bits
    M, S = 101, set(range(102))
    for _ in range(2):
        S = {snap(4.0, M, k) for k in S}
    assert math.log2(M + 1) - math.log2(len(S)) < 2
    # circular doubling, M = 2^a m: |image of t steps| = 2^(a - min(t, a)) m exactly
    for M in [1000, 1024, 3 * 2 ** 5 * 7, 2 ** 4 * 45, 999]:
        a, m = split2(M)
        S = set(range(M))
        for t in range(a + 4):
            assert len({2 ** t * k % M for k in range(M)}) == 2 ** (a - min(t, a)) * m
            assert len(S) == 2 ** (a - min(t, a)) * m          # thm:dyn-circ-overflow
            S2 = {2 * k % M for k in S}
            if t >= a:
                assert S2 == S                                 # bijection on the cycle states
            S = S2
    print("\nchannel capacity of the state: log2(M+1) bits on [0,1]; every symmetric step "
          "loses >= 1 bit for odd M; circular doubling overflows exactly min(t, a) bits")


def main():
    check_circle()
    check_xrounded()
    check_horizons()
    check_cat()
    check_reversible()
    check_cascade()
    check_capacity()
    print("OK 17_periods_overflow")


if __name__ == "__main__":
    main()

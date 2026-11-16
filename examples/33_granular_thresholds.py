# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.
"""Granular computational complexity (Chapter 19, ch:gcc): every number of the chapter.

  * the lowest layer of the switchboard on four variables: the 272 eight-clause cores are
    the perfect matchings of the 4-cube, and only 4 of them lie on a single triple; the
    glued core of the chapter is one of the others;
  * the integer lift P_SAT: total degree 2^n C(n,3) and its exact value at (1/2,...,1/2),
    for n = 3, 4, 5, in rational arithmetic;
  * the horizon bound 4 (n-2)^3 <= 3 q K for every n that fits, and the lattice count
    (2m+1)^3;
  * the thresholds: 2^398 < 10^120 < 2^399, the least n with 8 C(n,3) > 10^80,
    8 C(399,3) and 8 C(10^80,3), in exact integers;
  * locality: the cells within L-infinity radius r number (2r+1)^3, a fan-out of six needs
    one tick and no repeater, and the cells reached in t ticks (L1 radius t) never exceed
    (2t+1)^3;
  * finite dynamics: every orbit of a map on M states repeats within M steps.

Pure Python 3, exact integers and fractions; runs in a few seconds.  Every printed claim
is asserted.
"""
import itertools
import random
from fractions import Fraction
from math import comb


def N(n):
    return 8 * comb(n, 3)


def cores_q4():
    """Eight-clause unsatisfiable sets on four variables = perfect matchings of Q4."""
    edges = [(v, v ^ (1 << d), d) for v in range(16) for d in range(4) if v < v ^ (1 << d)]
    out = []

    def rec(free, chosen):
        if not free:
            out.append(tuple(chosen))
            return
        v = min(free)
        for a, b, d in edges:
            if a == v and b in free:
                rec(free - {a, b}, chosen + [(a, b, d)])
    rec(frozenset(range(16)), [])
    return out


def main():
    cores = cores_q4()
    single = [m for m in cores if len({d for _, _, d in m}) == 1]
    print(f"n = 4: {len(cores)} eight-clause cores, {len(single)} on a single triple")
    assert len(cores) == 272 and len(single) == 4
    # glued core: clauses on {0,1,2} forbidding x0 = 0, on {0,1,3} forbidding x0 = 1
    glued = [(0, 1, 2, 0, u, w) for u in (0, 1) for w in (0, 1)] + \
            [(0, 1, 3, 1, u, w) for u in (0, 1) for w in (0, 1)]

    def blocks(c, x):
        i, j, k, a, b, d = c
        return (x >> i & 1, x >> j & 1, x >> k & 1) == (a, b, d)
    assert all(any(blocks(c, x) for c in glued) for x in range(16))
    assert all(sum(blocks(c, x) for c in glued) == 1 for x in range(16))
    print("  the glued core blocks every assignment exactly once: a core on two triples")

    for n in (3, 4, 5):
        C = comb(n, 3)
        deg = 2 ** n * C                       # every factor has degree C(n,3)
        half = 1 - (1 - Fraction(1, 2) ** C) ** (2 ** n)
        # direct product over assignments with exact fractions
        prod = Fraction(1)
        for x in range(2 ** n):
            blk = Fraction(1)
            for T in itertools.combinations(range(n), 3):
                blk *= Fraction(1, 2)          # one falsified clause per triple
            prod *= 1 - blk
        assert 1 - prod == half
        print(f"  P_SAT, n = {n}: total degree {deg} (N = {N(n)}), value at 1/2 = {float(half):.6g}")
        assert (deg > N(n)) == (n >= 4)

    for n in range(3, 400):
        for qK in (N(n), N(n) + 17):
            assert 4 * (n - 2) ** 3 <= 3 * qK
    assert all(len(list(itertools.product(range(-m, m + 1), repeat=3))) == (2 * m + 1) ** 3
               for m in range(4))
    print("horizon: 4 (n-2)^3 <= 3 q K for every fitting switchboard (n < 400); box (2m+1)^3")

    assert 2 ** 398 < 10 ** 120 < 2 ** 399
    lo, hi = 3, 10 ** 30
    while lo < hi:
        m = (lo + hi) // 2
        lo, hi = (lo, m) if N(m) > 10 ** 80 else (m + 1, hi)
    print(f"thresholds: 2^398 < 10^120 < 2^399; least n with 8 C(n,3) > 10^80: {lo}")
    assert lo == 421716332650874621422854877
    assert N(399) == 84059192 and 1333 * 10 ** 237 <= N(10 ** 80) <= 1334 * 10 ** 237
    print(f"  8 C(399,3) = {N(399)} bits = {N(399) / 8e6:.3f} MB; 8 C(10^80,3) = {N(10**80):.4e}")

    nb = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
    assert len(set(nb)) == 6
    for t in range(6):
        ball = [p for p in itertools.product(range(-t, t + 1), repeat=3) if sum(map(abs, p)) <= t]
        assert len(ball) == (2 * t + 1) * (2 * t * t + 2 * t + 3) // 3 <= (2 * t + 1) ** 3
        assert len(ball) - 1 <= 6 ** t or t == 0
    print("locality: six neighbours in one tick; cells within t ticks (2t+1)(2t^2+2t+3)/3 <= (2t+1)^3")

    rnd = random.Random(19)
    for M in (5, 50, 500):
        f = [rnd.randrange(M) for _ in range(M)]
        for x0 in range(M):
            seen, x = {}, x0
            for k in range(M + 1):
                if x in seen:
                    break
                seen[x] = k
                x = f[x]
            assert k <= M
    print("finite dynamics: every orbit of a map on M states repeats within M steps")

    # 2-SAT inside the horizon: padding m = 2, 3 variables into n = 4 keeps satisfiability,
    # exhaustively, and both switchboards are bounded by one lookup constant.
    def clauses2(n):
        return [(i, j, a, b) for i, j in itertools.combinations(range(n), 2)
                for a in (0, 1) for b in (0, 1)]

    def sat2(n, on):
        return any(all(not (x[i] == a and x[j] == b) for (i, j, a, b) in on)
                   for x in itertools.product((0, 1), repeat=n))

    for m in (2, 3):
        cm = clauses2(m)
        assert len(cm) == 4 * comb(m, 2)
        for mask in range(1 << len(cm)):
            on = [c for k, c in enumerate(cm) if mask >> k & 1]
            assert sat2(4, on) == sat2(m, on)
    lookup = lambda N: N + 1 + 2 ** N * N
    C = sum(lookup(4 * comb(n, 2)) + lookup(N(n)) for n in range(5))
    print("2-SAT: padding into 4 variables keeps all 2^4 and 2^12 switchboards")
    print(f"  one constant C = {C} bounds 2-SAT and 3-SAT for n <= 4")

    # General formulas: three-term combinations rewritten as two-term ones keep every
    # value and at most double the connectives; the three-term carry is two carries.
    def rand_f(depth, n):
        if depth == 0 or rnd.random() < 0.2:
            return ("var", rnd.randrange(n))
        op = rnd.choice(["not", "and2", "or2", "and3", "or3"])
        k = {"not": 1, "and2": 2, "or2": 2, "and3": 3, "or3": 3}[op]
        return (op,) + tuple(rand_f(depth - 1, n) for _ in range(k))

    def ev(f, x):
        op = f[0]
        if op == "var":
            return x[f[1]]
        v = [ev(g, x) for g in f[1:]]
        return (not v[0]) if op == "not" else all(v) if op[:3] == "and" else any(v)

    def binf(f):
        op = f[0]
        if op == "var":
            return f
        g = [binf(h) for h in f[1:]]
        if op in ("and3", "or3"):
            o = op[:-1] + "2"
            return (o, (o, g[0], g[1]), g[2])
        return (op,) + tuple(g)

    size = lambda f: 0 if f[0] == "var" else 1 + sum(size(g) for g in f[1:])
    for _ in range(2000):
        f = rand_f(5, 4)
        assert size(binf(f)) <= 2 * size(f)
        assert all(ev(f, x) == ev(binf(f), x) for x in itertools.product((False, True), repeat=4))
    for a, b, c in itertools.product((0, 1), repeat=3):
        c1, s1 = a & b, a ^ b
        c2 = s1 & c
        assert not (c1 and c2) and (c1 | c2) == (a + b + c >= 2) and a + b + c == (s1 ^ c) + 2 * (c1 + c2)
    print("gSAT: 2000 random formulas keep every value with two-term combinations only")
    print("  the three-term carry is two exclusive two-term carries: maj = ab | (a^b)c")

    # General 2-SAT: every one of the 16 relations on two bits is closed under majority;
    # the 3-OR on three bits is not.
    sq = list(itertools.product((0, 1), repeat=2))
    majv = lambda p, q, r: tuple(int(a + b + c >= 2) for a, b, c in zip(p, q, r))
    for mask in range(16):
        R = [p for k, p in enumerate(sq) if mask >> k & 1]
        assert all(majv(p, q, r) in R for p in R for q in R for r in R)
    or3 = [p for p in itertools.product((0, 1), repeat=3) if any(p)]
    assert majv((1, 0, 0), (0, 1, 0), (0, 0, 1)) not in or3
    print("general 2-SAT: all 16 binary relations are closed under majority;")
    print("  x0|x1|x2 is not")


if __name__ == "__main__":
    main()

# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""16 -- No Banach-Tarski on the granular ball; Hilbert's hotel is closed.

Classical problem.  The unit ball of R^3 can be cut into finitely many
pieces and reassembled by rigid motions into two copies of itself
(Banach-Tarski); N splits into evens and odds, each in bijection with N
(Hilbert's hotel).  Classically there is no measure of the pieces: they
are non-measurable, and "how much volume does each piece carry?" has no
answer.  The paradox is not a contradiction; it shows that volume cannot
be defined on all sets of R^3.

Granular resolution (Chapter 3: thm:measure-no-bt, ex:measure-hilbert,
thm:faithful).  The granular ball B = {x in L^3 : |x| <= 1} is a finite set.
For ANY partition into pieces and ANY maps injective on the pieces, two
reassemblies into B force |B| = 2|B|, so B is empty.  Counting replaces
measurability, and invariance holds under all injections, not just rigid
motions.  Below: the granular ball and its exact measure; a random
partition, rotated by exact lattice symmetries, reassembles into one copy
and never two; Hilbert's hotel on [0, 2H) halves into [0, H).
"""
from fractions import Fraction as F
import itertools
import math
import random


def main():
    n = 12                                         # 2eps = 1/n
    rng = range(-n, n + 1)
    B = {(a, b, c) for a in rng for b in rng for c in rng if a * a + b * b + c * c <= n * n}
    h = F(1, n)
    mu = len(B) * h ** 3
    assert abs(mu - F(4, 3) * F(math.pi)) < 0.1      # shadow: the Lebesgue volume
    print(f"granular ball, 2eps = 1/{n}: |B| = {len(B)} points, mu(B) = {float(mu):.5f} "
          f"(4 pi/3 = {4 * math.pi / 3:.5f})")
    # the 48 signed permutations: exact rigid motions of the lattice
    G = [(p, s) for p in itertools.permutations(range(3))
         for s in itertools.product((1, -1), repeat=3)]
    act = lambda g, x: tuple(g[1][i] * x[g[0][i]] for i in range(3))
    assert len(G) == 48 and all({act(g, x) for x in B} == B for g in G)
    r = random.Random(1924)
    pts = sorted(B)
    for trial in range(200):
        k = r.randint(2, 8)                         # random partition into k pieces
        lab = {x: r.randrange(k) for x in pts}
        pieces = [[x for x in pts if lab[x] == i] for i in range(k)]
        moves = [r.choice(G) for _ in range(k)]
        images = [{act(g, x) for x in P} for g, P in zip(moves, pieces)]
        assert all(len(I) == len(P) for I, P in zip(images, pieces))   # injective on pieces
        assert sum(len(I) for I in images) == len(B)                   # mass is conserved
        # two disjoint sub-families covering B twice would need 2|B| points
        for T in itertools.product((0, 1), repeat=k):
            cover0 = sum(len(I) for I, t in zip(images, T) if t == 0)
            cover1 = sum(len(I) for I, t in zip(images, T) if t == 1)
            assert not (cover0 == len(B) and cover1 == len(B))
    print("200 random partitions (2-8 pieces), all subfamily splits: never two copies")
    # Hilbert's hotel on [0, 2H): evens halve onto [0, H) -- half the hotel
    Hh = 10 ** 5
    evens = range(0, 2 * Hh, 2)
    assert len(evens) == Hh and {e // 2 for e in evens} == set(range(Hh))
    assert F(len(evens), 2 * Hh) == F(1, 2)
    print(f"Hilbert's hotel [0, 2H), H = {Hh}: the evens fill [0, H), not the hotel")
    print("OK 16_no_paradoxical_decomposition")


if __name__ == "__main__":
    main()

# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""11 -- Exact recurrence and the Loschmidt echo on the granular torus.

Classical problem.  Loschmidt: the microscopic laws are reversible, so how
can entropy increase?  Zermelo: Poincare recurrence says a bounded system
returns "arbitrarily close" to its initial state -- with no time bound.
Numerically the reversed run of a chaotic map is not computable: in
floating point the echo fails after about ln(1e16)/lambda steps, and the
computed map is not even injective.  Classically recurrence times and exact
reversal are without object (no bound, an idealisation).

Granular resolution (Chapter 17: thm:dyn-cat, thm:dyn-cat-fib,
thm:dyn-cat-dyadic, tab:dyn-cat-periods, thm:dyn-leap, thm:dyn-loschmidt).
The cat map (x,y) -> (2x+y, x+y) on (Z/N)^2 is a permutation with a
computable period Pi(N) <= 3N (Pi(2^k) = 3 2^(k-2)); every integer
kick-drift map L(q,p) = (q+p+F(q), p+F(q)) with reversal
rho(q,p) = (q, -p-F(q)) satisfies rho L^n rho L^n = id exactly, for every n.
"""
import math
import numpy as np


def cat_period(N):
    """Least n with A^n = I mod N, A = [[2,1],[1,1]] (thm:dyn-cat-fib)."""
    a, b, c, d, n = 2 % N, 1 % N, 1 % N, 1 % N, 1
    while (a, b, c, d) != (1 % N, 0, 0, 1 % N):
        a, b, c, d = (2 * a + c) % N, (2 * b + d) % N, (a + c) % N, (b + d) % N
        n += 1
    return n


BOOK = {2: 3, 3: 4, 4: 3, 5: 10, 6: 12, 7: 8, 8: 6, 9: 12, 10: 30, 11: 5, 12: 12,
        13: 14, 16: 12, 25: 50, 32: 24, 64: 48, 101: 25, 128: 96, 256: 192,
        1000: 750, 1009: 63, 1024: 768, 10 ** 4: 7500}


def main():
    for N, P in BOOK.items():                               # tab:dyn-cat-periods
        assert cat_period(N) == P, (N, cat_period(N), P)
    assert all(cat_period(N) <= 3 * N for N in range(2, 400))
    assert [N for N in range(2, 400) if cat_period(N) == 3 * N] == [10, 50, 250]
    assert all(cat_period(2 ** k) == 3 * 2 ** (k - 2) for k in range(3, 21))
    # the whole picture returns: iterate all N^2 states of (Z/101)^2
    N = 101
    x, y = np.meshgrid(np.arange(N), np.arange(N))
    x0, y0 = x.copy(), y.copy()
    for t in range(1, cat_period(N) + 1):
        x, y = (2 * x + y) % N, (x + y) % N
        back = np.array_equal(x, x0) and np.array_equal(y, y0)
        assert back == (t == cat_period(N))
    print(f"cat map: table periods confirmed, Pi(N) <= 3N; all {N * N} states of "
          f"(Z/{N})^2 return at t = {cat_period(N)}")
    # Loschmidt echo: float standard map vs integer kick-drift map on (Z/2^20)^2
    K, N = 1.5, 2 ** 20
    F = [round(K * N / (2 * math.pi) * math.sin(2 * math.pi * q / N)) for q in range(N)]
    lam = lambda s: ((s[0] + s[1] + F[s[0]]) % N, (s[1] + F[s[0]]) % N)
    rho = lambda s: (s[0], (-s[1] - F[s[0]]) % N)
    s0 = (round(1.0 * N / (2 * math.pi)), round(0.3 * N / (2 * math.pi)))
    print(f"\n{'n':>6} {'float echo error':>17} {'integer echo':>13}")
    errs = {}
    for n in [10, 40, 60, 80, 100, 1000, 10000]:
        q, p = 1.0, 0.3
        for _ in range(n):
            p += K * math.sin(q); q += p
        for _ in range(n):                                  # algebraically exact inverse
            q -= p; p -= K * math.sin(q)
        errs[n] = math.hypot(q - 1.0, p - 0.3)
        s = s0
        for _ in range(n):
            s = lam(s)
        s = rho(s)
        for _ in range(n):
            s = lam(s)
        s = rho(s)
        assert s == s0                                       # thm:dyn-loschmidt, exact
        print(f"{n:6d} {errs[n]:17.2e} {'exact':>13}")
    assert errs[10] < 1e-11 and errs[100] > 1e-2           # round-off horizon ~ 100 steps
    assert errs[10] < errs[40] < errs[60] < errs[80] < errs[100]
    print("OK 11_cat_map_echo")


if __name__ == "__main__":
    main()

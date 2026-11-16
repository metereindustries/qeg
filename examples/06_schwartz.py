# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""06 -- Products of distributions: Schwartz's impossibility, granularly.

Classical problem.  delta*delta has no meaning in D'.  Schwartz (1954): no
associative algebra containing D' with an exact Leibniz rule and the usual
product of continuous functions can multiply distributions; e.g. the chain
    0 = (delta x) vp(1/x) = delta (x vp(1/x)) = delta * 1 = delta
is a contradiction.  Classically the products are without object, or need
ad hoc regularisation/association (Colombeau), and "H delta" has three
answers in circulation (undefined, delta/2, delta/(n+1) for H^n delta).

Granular resolution (Chapter 6: def:analysis-delta, thm:analysis-delta-square,
thm:analysis-pv, thm:analysis-H-squared, thm:analysis-heaviside-products).
On the lattice x = 2eps*k, delta_eps = 1/(2eps) at 0 and 0 elsewhere is an
ordinary function; pointwise products are associative and exact:
    delta^2 = delta/(2eps),   x vp = 1 - 2eps delta,   delta (x vp) = 0,
    delta = 2 H delta - 2eps delta^2,   H delta = delta.
The term Schwartz's chain drops (2eps delta, the indicator of the one
point-sphere at 0) becomes 2eps delta^2 = delta after multiplication by delta.
"""
from fractions import Fraction as F

K = 6                                     # window k = -K..K
h = F(1, 1000)                            # 2 eps
X = [h * k for k in range(-K, K + 1)]     # lattice points
I0 = K                                    # index of x = 0


def fn(f):
    return [F(f(x)) for x in X]


def mul(*us):
    out = [F(1)] * len(X)
    for u in us:
        out = [a * b for a, b in zip(out, u)]
    return out


def scale(c, u):
    return [c * a for a in u]


def add(u, v):
    return [a + b for a, b in zip(u, v)]


def Dm(u):                                 # backward difference (u(x)-u(x-2eps))/2eps
    return [None] + [(u[i] - u[i - 1]) / h for i in range(1, len(u))]


def pair(u, phi):                          # <u, phi> = sum u phi 2eps
    return sum(a * b for a, b in zip(u, phi)) * h


def trim(u):                               # drop the left boundary point of the window
    return u[1:]


def main():
    delta = fn(lambda x: 1 / h if x == 0 else 0)
    H = fn(lambda x: 1 if x >= 0 else 0)                 # closed half-line
    Htheta = lambda th: fn(lambda x: 1 if x > 0 else (th if x == 0 else 0))
    pv = fn(lambda x: 1 / x if x != 0 else 0)
    x = fn(lambda x: x)
    one = fn(lambda x: 1)
    phi = fn(lambda x: 3 + x - 7 * x * x)               # a test function, phi(0) = 3

    assert pair(delta, phi) == phi[I0]
    assert mul(delta, delta) == scale(1 / h, delta)            # delta^2 = delta/(2eps)
    assert pair(mul(delta, delta), phi) == phi[I0] / h
    assert mul(delta, delta, delta) == scale(1 / h ** 2, delta)
    assert mul(x, delta) == [0] * len(X)                        # x delta = 0
    xpv = mul(x, pv)
    assert xpv == add(one, scale(-h, delta))                    # x vp = 1 - 2eps delta
    assert mul(delta, xpv) == mul(mul(delta, x), pv) == [0] * len(X)   # associative
    assert scale(h, mul(delta, delta)) == delta                 # the dropped term
    assert trim(Dm(H)) == trim(delta)                           # Dm H = delta
    assert mul(H, H) == H
    lhs = trim(delta)                                           # Leibniz with cross term
    rhs = trim(add(scale(2, mul(H, delta)), scale(-h, mul(delta, delta))))
    assert lhs == rhs
    assert mul(H, delta) == delta                               # H delta = delta, not delta/2
    for th in [F(0), F(1, 2), F(1)]:
        for n in [1, 2, 3]:
            assert mul(*([Htheta(th)] * n), delta) == scale(th ** n, delta)
    Hs = H[:-1]                                                 # H(x - 2eps) on the window
    strat = [(a + b) / 2 * d for a, b, d in zip(Hs, H[1:], trim(Dm(H)))]
    assert strat == scale(F(1, 2), trim(delta))                 # midpoint reading: delta/2

    rows = [("delta^2", "undefined", "delta/(2eps)"),
            ("x vp(1/x)", "1", "1 - 2eps delta"),
            ("delta (x vp)", "delta  (=> delta = 0)", "0"),
            ("(delta x) vp", "0", "0"),
            ("2eps delta^2", "dropped", "delta"),
            ("H delta", "delta/2 or undefined", "delta (H closed)"),
            ("H_theta^n delta", "delta/(n+1) (assoc.)", "theta^n delta")]
    print(f"2eps = {h}, window k = -{K}..{K}; value at 0 of delta: {delta[I0]}")
    print(f"{'product':16} {'classical':24} {'granular (exact)':18}")
    for r in rows:
        print(f"{r[0]:16} {r[1]:24} {r[2]:18}")
    print(f"<delta^2, phi> = phi(0)/(2eps) = {pair(mul(delta, delta), phi)}")
    print("OK 06_schwartz")


if __name__ == "__main__":
    main()

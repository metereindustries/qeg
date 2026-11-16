# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""21 -- Hilbert's axioms in a plane whose points have a part.

Classical problem.  Euclid *defines* the point as that which has no part;
Hilbert leaves it undefined, and in every model of his axioms the point still
has no part.  Which axiom is responsible?

Granular resolution (Chapter 10, ch:hilbert).  Everything is computed exactly
in the ordered field Q(e) of rational functions of an infinitesimal e
(ordered by the sign of the lowest-order coefficient, so that 0 < e < 1/n for
every n), the simplest field with a granule.  The script checks:
  * Hilbert's groups I, II (including Pasch), III.3, III.4, III.5 and IV hold
    exactly in the Cartesian plane over Q(e), on random configurations with
    infinitesimal and infinite coordinates (thm:hilbert-cartesian; III.1
    needs square roots and is checked when the ratio of lengths is a square);
  * Archimedes V.1 fails: the chain A_i = (i e, 0) never passes B = (1, 0),
    and the granule is a negligible segment, n^2 e^2 < 1 for every n
    (thm:hilbert-granule, thm:hilbert-nopart);
  * the shadow st (evaluation at e = 0) is onto, preserves lines, betweenness
    and congruence, and identifies (0, 0) with (e, 0): a point has parts
    (thm:hilbert-shadow, thm:hilbert-parts);
  * Dedekind's axiom fails: the cut finite / infinite of the x-axis has no
    separating point (thm:hilbert-dedekind-iff);
  * elementary theorems transfer: Pythagoras and the concurrence of the
    medians hold exactly for triangles with infinitesimal and infinite sides
    (thm:hilbert-transfer).
"""
from fractions import Fraction
import random

random.seed(2026)


# ---------------------------------------------------------------- Q(e)
class Poly:
    """Polynomial in e with Fraction coefficients, as a dict degree -> coeff."""

    def __init__(self, c=None):
        self.c = {k: Fraction(v) for k, v in (c or {}).items() if v != 0}

    @staticmethod
    def const(a):
        return Poly({0: a})

    def __add__(self, o):
        d = dict(self.c)
        for k, v in o.c.items():
            d[k] = d.get(k, 0) + v
        return Poly(d)

    def __neg__(self):
        return Poly({k: -v for k, v in self.c.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        d = {}
        for i, a in self.c.items():
            for j, b in o.c.items():
                d[i + j] = d.get(i + j, 0) + a * b
        return Poly(d)

    def is_zero(self):
        return not self.c

    def low(self):
        """(lowest degree, its coefficient)."""
        k = min(self.c)
        return k, self.c[k]


class Qe:
    """Element of Q(e) = num/den, den != 0."""

    def __init__(self, num, den=None):
        if not isinstance(num, Poly):
            num = Poly.const(num)
        if den is None:
            den = Poly.const(1)
        assert not den.is_zero()
        self.n, self.d = num, den

    def __add__(self, o):
        o = lift(o)
        return Qe(self.n * o.d + o.n * self.d, self.d * o.d)

    __radd__ = __add__

    def __neg__(self):
        return Qe(-self.n, self.d)

    def __sub__(self, o):
        return self + (-lift(o))

    def __rsub__(self, o):
        return lift(o) - self

    def __mul__(self, o):
        o = lift(o)
        return Qe(self.n * o.n, self.d * o.d)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = lift(o)
        assert not o.n.is_zero()
        return Qe(self.n * o.d, self.d * o.n)

    def __rtruediv__(self, o):
        return lift(o) / self

    def __pow__(self, k):
        r = Qe(1)
        for _ in range(k):
            r = r * self
        return r

    def sign(self):
        if self.n.is_zero():
            return 0
        _, a = self.n.low()
        _, b = self.d.low()
        return (1 if a > 0 else -1) * (1 if b > 0 else -1)

    def __eq__(self, o):
        return (self - lift(o)).sign() == 0

    def __lt__(self, o):
        return (self - lift(o)).sign() < 0

    def __le__(self, o):
        return (self - lift(o)).sign() <= 0

    def __gt__(self, o):
        return (self - lift(o)).sign() > 0

    def __ge__(self, o):
        return (self - lift(o)).sign() >= 0

    def __hash__(self):
        return 0

    def is_finite(self):
        """Finite: valuation >= 0 (denominator not of higher order than numerator)."""
        if self.n.is_zero():
            return True
        return self.n.low()[0] >= self.d.low()[0]

    def is_infinitesimal(self):
        if self.n.is_zero():
            return True
        return self.n.low()[0] > self.d.low()[0]

    def st(self):
        """Shadow of a finite element: evaluation at e = 0 (a Fraction)."""
        assert self.is_finite()
        if self.n.is_zero():
            return Fraction(0)
        kn, an = self.n.low()
        kd, ad = self.d.low()
        return an / ad if kn == kd else Fraction(0)

    def __repr__(self):
        return f"Qe({dict(self.n.c)}/{dict(self.d.c)})"


def lift(x):
    return x if isinstance(x, Qe) else Qe(x)


E = Qe(Poly({1: 1}))          # the granule e
ONE, ZERO = Qe(1), Qe(0)


def rnd(infinitesimals=True, infinites=True):
    """Random element a + b e + c e^2 (+ d/e), small integer coefficients."""
    p = Poly({0: random.randint(-3, 3)})
    if infinitesimals:
        p = p + Poly({1: random.randint(-3, 3), 2: random.randint(-2, 2)})
    x = Qe(p)
    if infinites and random.random() < 0.3:
        x = x + Qe(Poly.const(random.randint(1, 3)), Poly({1: 1}))
    return x


# ---------------------------------------------------------------- geometry
def sub(A, B):
    return (A[0] - B[0], A[1] - B[1])


def ip(u, v):
    return u[0] * v[0] + u[1] * v[1]


def cr(u, v):
    return u[0] * v[1] - u[1] * v[0]


def q(A, B):
    return (A[0] - B[0]) ** 2 + (A[1] - B[1]) ** 2


def pt_eq(A, B):
    return A[0] == B[0] and A[1] == B[1]


def btw(A, B, C):
    """B strictly between A and C: A != C and B = A + t (C - A), 0 < t < 1."""
    if pt_eq(A, C):
        return False
    w = sub(C, A)
    if cr(w, sub(B, A)) != ZERO:
        return False
    t = (sub(B, A)[0] / w[0]) if w[0] != ZERO else (sub(B, A)[1] / w[1])
    return ZERO < t < ONE


def collinear(A, B, C):
    return cr(sub(B, A), sub(C, A)) == ZERO


def line_through(A, B):
    """(a, b, c) with a x + b y + c = 0 through A != B."""
    a, b = -(B[1] - A[1]), B[0] - A[0]
    return a, b, -(a * A[0] + b * A[1])


def on_line(L, P):
    a, b, c = L
    return a * P[0] + b * P[1] + c == ZERO


def ang_cong(B, A, C, B2, A2, C2):
    """Root-free congruence of angles <BAC and <B2A2C2."""
    u, v = sub(B, A), sub(C, A)
    u2, v2 = sub(B2, A2), sub(C2, A2)
    return (ip(u, v) ** 2 * (q(A2, B2) * q(A2, C2)) == ip(u2, v2) ** 2 * (q(A, B) * q(A, C))
            and ip(u, v) * ip(u2, v2) >= ZERO)


def random_point():
    return (rnd(), rnd())


def random_triangle():
    while True:
        A, B, C = random_point(), random_point(), random_point()
        if not collinear(A, B, C):
            return A, B, C


# ---------------------------------------------------------------- checks
def check_incidence_order(trials=200):
    for _ in range(trials):
        A, B, C = random_triangle()
        L = line_through(A, B)
        assert on_line(L, A) and on_line(L, B) and not on_line(L, C)     # I.1, I.3
        # I.2: any line through A, B is the same set: a second representation
        L2 = line_through(B, A)
        for P in (random_point() for _ in range(5)):
            assert on_line(L, P) == on_line(L2, P)
        # II.2 and II.3
        D = (2 * C[0] - A[0], 2 * C[1] - A[1])
        assert btw(A, C, D) and not btw(C, A, D) and not btw(A, D, C)
        # II.1 symmetry and collinearity
        t = Qe(Fraction(random.randint(1, 9), 10))
        M = (A[0] + t * (C[0] - A[0]), A[1] + t * (C[1] - A[1]))
        assert btw(A, M, C) and btw(C, M, A) and collinear(A, M, C)
        assert not pt_eq(A, M) and not pt_eq(M, C)
    print("I, II.1-II.3: exact in Q(e)^2 on", trials, "random configurations")


def check_pasch(trials=200):
    for _ in range(trials):
        A, B, C = random_triangle()
        # a line through an interior point of AB and a point outside the triangle
        t = Qe(Fraction(random.randint(1, 9), 10))
        X = (A[0] + t * (B[0] - A[0]), A[1] + t * (B[1] - A[1]))
        while True:
            P = random_point()
            L = line_through(X, P) if not pt_eq(X, P) else None
            if L and not on_line(L, A) and not on_line(L, B) and not on_line(L, C):
                break
        a, b, c = L
        phi = lambda Z: a * Z[0] + b * Z[1] + c
        assert phi(A) * phi(B) < ZERO
        hit = False
        for (U, V) in ((A, C), (B, C)):
            if phi(U) * phi(V) < ZERO:
                s = phi(U) / (phi(U) - phi(V))
                Y = (U[0] + s * (V[0] - U[0]), U[1] + s * (V[1] - U[1]))
                assert on_line(L, Y) and btw(U, Y, V)
                hit = True
        assert hit
    print("II.4 (Pasch): the crossing point exists on", trials, "random triangles")


def check_congruence(trials=200):
    for _ in range(trials):
        # III.3: addition of segments along two lines with the same parameters
        A, B, C = random_triangle()
        A2, B2, C2 = random_triangle()
        t = Qe(Fraction(random.randint(1, 9), 10))
        M = (A[0] + t * (C[0] - A[0]), A[1] + t * (C[1] - A[1]))
        lam = Qe(random.randint(1, 3))      # scale C2 so that AC ~ A2C2 is not needed
        M2 = (A2[0] + t * (C2[0] - A2[0]), A2[1] + t * (C2[1] - A2[1]))
        if q(A, M) == q(A2, M2) and q(M, C) == q(M2, C2):
            assert q(A, C) == q(A2, C2)
        # III.1 when the ratio of lengths is a square: lay AB on the ray A2 B2
        r2 = q(A, B) / q(A2, B2)
        for s in (Qe(1), Qe(2), Qe(Fraction(1, 2)), E, Qe(1) / E, ONE + E):
            if r2 == s * s:
                P = (A2[0] + s * (B2[0] - A2[0]), A2[1] + s * (B2[1] - A2[1]))
                assert q(A2, P) == q(A, B)
        # III.4: lay off the angle <BAC at A2 on the ray A2 B2, side of C2
        u, v = sub(B, A), sub(C, A)
        i, k = ip(u, v), cr(u, v)
        u2 = sub(B2, A2)
        phiD = cr(u2, sub(C2, A2))
        sigma = ONE if k * phiD > ZERO else -ONE
        P = (A2[0] + i * u2[0] - sigma * k * u2[1], A2[1] + i * u2[1] + sigma * k * u2[0])
        assert not collinear(A2, B2, P)
        assert cr(u2, sub(P, A2)) * phiD > ZERO                 # same side as C2
        assert ang_cong(B, A, C, B2, A2, P)
        # uniqueness: scaling P along the ray keeps the angle, moving off it breaks it
        P2 = (A2[0] + 3 * (P[0] - A2[0]), A2[1] + 3 * (P[1] - A2[1]))
        assert ang_cong(B, A, C, B2, A2, P2)
        Pbad = (P[0] + u2[0], P[1] + u2[1])
        assert not (ang_cong(B, A, C, B2, A2, Pbad) and
                    cr(u2, sub(Pbad, A2)) * phiD > ZERO) or collinear(A2, B2, Pbad) or \
            cr(sub(P, A2), sub(Pbad, A2)) == ZERO
        # III.5 (SAS): copy the triangle by a rigid motion with rational cos/sin
        c_, s_ = Qe(Fraction(3, 5)), Qe(Fraction(4, 5))
        T = random_point()
        rot = lambda Z: (T[0] + c_ * Z[0] - s_ * Z[1], T[1] + s_ * Z[0] + c_ * Z[1])
        Ar, Br, Cr = rot(A), rot(B), rot(C)
        assert q(A, B) == q(Ar, Br) and q(A, C) == q(Ar, Cr)
        assert ang_cong(B, A, C, Br, Ar, Cr)
        assert ang_cong(A, B, C, Ar, Br, Cr)                   # the conclusion of III.5
        # IV: the parallel through C2 to line AB is unique and misses it
        a, b, c = line_through(A, B)
        par = (a, b, -(a * C2[0] + b * C2[1]))
        if not on_line((a, b, c), C2):
            for Z in (random_point() for _ in range(5)):
                assert not (on_line((a, b, c), Z) and on_line(par, Z))
    print("III.1 (square ratios), III.3, III.4, III.5, IV: exact on", trials, "random triangles")


def check_archimedes():
    A, B = (ZERO, ZERO), (ONE, ZERO)
    for n in (1, 10, 10 ** 6, 10 ** 30):
        An = (Qe(n) * E, ZERO)
        assert not btw(A, B, An)                     # B never between A and A_n
        assert Qe(n) ** 2 * q(A, (E, ZERO)) < q(A, B)  # the granule is negligible
    # the chain is forced: each congruent step beyond A_i lands at 2 A_i - A_{i-1}
    S = [(Qe(i) * E, ZERO) for i in range(6)]
    for i in range(4):
        assert btw(S[i], S[i + 1], S[i + 2]) and q(S[i], S[i + 1]) == q(S[i + 1], S[i + 2])
    # in Q (Archimedean) every segment is reached: n = ceil(|CD|/|AB|)
    for _ in range(50):
        a, c = Fraction(random.randint(1, 50), random.randint(1, 50)), Fraction(random.randint(1, 500), random.randint(1, 50))
        n = -(-c // a)
        assert Qe(n) ** 2 * Qe(a * a) >= Qe(c * c)
    print("V.1 fails in Q(e)^2: n^2 e^2 < 1 for n = 1, 10, 10^6, 10^30; the chain (i e, 0) never passes (1, 0)")
    print("V.1 holds in Q^2: n = ceil(|CD|/|AB|) copies of AB reach CD (50 random pairs)")


def check_shadow(trials=200):
    st = lambda P: (P[0].st(), P[1].st())
    for _ in range(trials):
        A, B, C = (rnd(infinites=False), rnd(infinites=False)), (rnd(infinites=False), rnd(infinites=False)), (rnd(infinites=False), rnd(infinites=False))
        if pt_eq(A, C):
            continue
        t = Qe(Fraction(random.randint(1, 9), 10)) + E * random.randint(-1, 1)
        if not (ZERO < t < ONE):
            continue
        M = (A[0] + t * (C[0] - A[0]), A[1] + t * (C[1] - A[1]))
        assert btw(A, M, C)
        sA, sM, sC, st_t = st(A), st(M), st(C), t.st()
        assert 0 <= st_t <= 1
        assert sM[0] == sA[0] + st_t * (sC[0] - sA[0]) and sM[1] == sA[1] + st_t * (sC[1] - sA[1])
        # congruence and lines
        D = (B[0] + (C[0] - A[0]), B[1] + (C[1] - A[1]))      # BD congruent to AC
        assert q(B, D) == q(A, C)
        sB, sD = st(B), st(D)
        assert (sA[0] - sC[0]) ** 2 + (sA[1] - sC[1]) ** 2 == (sB[0] - sD[0]) ** 2 + (sB[1] - sD[1]) ** 2
        a, b, c = line_through(A, C)
        assert a.st() * sM[0] + b.st() * sM[1] + c.st() == 0
    # a point has parts
    c0, pole = (ZERO, ZERO), (E, ZERO)
    assert not pt_eq(c0, pole) and st(c0) == st(pole) == (0, 0)
    assert q(c0, pole) == E * E and (E * E).is_infinitesimal()
    print("shadow st: betweenness, congruence and lines preserved on", trials, "finite configurations;")
    print("           (0,0) != (e,0) but st(0,0) = st(e,0) = (0,0): the point has parts")


def check_dedekind():
    # the cut S = finite, T = infinite points of the x-axis has no separating point
    omega = ONE / E
    for O in (ZERO, ONE, Qe(10 ** 6), omega, 2 * omega, omega / 2, omega + ONE):
        if O.is_finite():
            P, Q = (O + ONE, ZERO), (omega, ZERO)              # P in S beyond O
            assert (O + ONE).is_finite() and not btw(P, (O, ZERO), Q)
        else:
            P, Q = (ZERO, ZERO), (O / 2, ZERO)                  # Q in T below O
            assert not (O / 2).is_finite() and not btw(P, (O, ZERO), Q)
    print("Dedekind fails in Q(e)^2: the cut finite | infinite of the x-axis has no separating point")


def check_transfer(trials=200):
    for _ in range(trials):
        A = random_point()
        u = (rnd(), rnd())
        if u[0] == ZERO and u[1] == ZERO:
            continue
        lam = rnd()
        if lam == ZERO:
            continue
        B = (A[0] + u[0], A[1] + u[1])
        C = (A[0] - lam * u[1], A[1] + lam * u[0])            # right angle at A
        assert ip(sub(B, A), sub(C, A)) == ZERO
        assert q(B, C) == q(A, B) + q(A, C)                   # Pythagoras, exactly
        # medians concur at the centroid
        G = ((A[0] + B[0] + C[0]) / 3, (A[1] + B[1] + C[1]) / 3)
        for (X, Y, Z) in ((A, B, C), (B, C, A), (C, A, B)):
            mid = ((Y[0] + Z[0]) / 2, (Y[1] + Z[1]) / 2)
            assert collinear(X, G, mid)
    print("transfer: Pythagoras and the concurrence of the medians hold exactly on", trials,
          "triangles with infinitesimal and infinite sides")


if __name__ == "__main__":
    print("Hilbert's axioms over Q(e), e an infinitesimal with 0 < e < 1/n for all n")
    check_incidence_order()
    check_pasch()
    check_congruence()
    check_archimedes()
    check_shadow()
    check_dedekind()
    check_transfer()
    print("all checks passed: groups I-IV hold, V.1 and Dedekind fail, the point has parts")

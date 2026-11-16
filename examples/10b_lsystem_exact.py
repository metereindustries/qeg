# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""10b -- Any generator becomes an exact L-system on the lattice.

Classical problem.  A self-similar curve is drawn by an L-system with a
turtle: F -> (turn, F, turn, F, ...), executed with real angles and real
lengths.  For a generator whose angles are not multiples of 90 degrees (the
60-degree Koch curve, or an angle of 1 radian, incommensurate with pi) the
turtle works in floating point: the drawn curve does not close exactly on
its base, and the same vertex reached along two branches of the computation
gets two slightly different coordinates.  Questions such as "how many times
does the curve touch itself?" are then decided by a tolerance.  This is a
limitation of the float computation, not of the classical curve, which is
the exact limit; but the classical curve is never what is computed.

Granular resolution (Chapter 12, Fractal Geometry).  Points are Gaussian
integers (pairs of ints): lattice point (k, l) means (k, l)*2eps.  A
generator is a list of lattice vertices p_0 = 0, ..., p_m = e with base
e (an integer vector).  The letters are the nonzero integer displacement
vectors v, and the rewrite rule is
    sigma(v) = [q_j - q_{j-1}]_{j=1..m},  q_j = round(p_j * v / e),
with complex multiplication and division done exactly in Fraction and
round(x) = floor(x + 1/2) componentwise (ties go towards +infinity).
Since q_0 = 0 and q_m = v exactly, the rewrite closes; zero letters are
dropped.  We check:
  1. the word sums to the axiom exactly at every depth, and the turtle path
     ends exactly at e; a float turtle on the unsnapped generator does not,
     and a shared vertex computed along two branches disagrees in low bits;
  2. for the quadratic Koch generator the system is the classical
     L-system F -> F+F-F-F+F, with 4 axis letters per depth;
  3. for the 60-degree Koch on the square lattice the alphabet grows, but
     the system stays exact, until the letters reach the granule;
  4. the number of repeated vertices (self-contacts) is an exact integer.
"""
from fractions import Fraction
import math
import numpy as np


# ---------- exact Gaussian-integer L-system ---------------------------------

def rnd(x):
    """Nearest integer, ties towards +infinity: floor(x + 1/2), exact on Fractions."""
    return math.floor(x + Fraction(1, 2))


def make_sigma(gen):
    """Rewrite rule of a generator gen = [p_0 = (0,0), ..., p_m = e] (integer pairs)."""
    ex, ey = gen[-1]
    n2 = ex * ex + ey * ey
    assert gen[0] == (0, 0) and n2 > 0
    memo = {}

    def sigma(v):
        if v not in memo:
            vx, vy = v
            q = []
            for px, py in gen:                          # p * v / e = p * v * conj(e) / |e|^2
                wx, wy = px * vx - py * vy, px * vy + py * vx
                zx = Fraction(wx * ex + wy * ey, n2)
                zy = Fraction(wy * ex - wx * ey, n2)
                q.append((rnd(zx), rnd(zy)))
            assert q[0] == (0, 0) and q[-1] == v        # closure, exactly
            memo[v] = [d for d in ((b[0] - a[0], b[1] - a[1]) for a, b in zip(q, q[1:]))
                       if d != (0, 0)]
        return memo[v]
    return sigma


def iterate(gen, K):
    """Words w_0 = [e], w_k = sigma(w_{k-1}); returns the list of words."""
    sigma = make_sigma(gen)
    words = [[gen[-1]]]
    for _ in range(K):
        words.append([d for v in words[-1] for d in sigma(v)])
    return words


def path(word):
    """Turtle path = exact partial sums (numpy int64; all values are small)."""
    a = np.array(word, dtype=np.int64)
    return np.vstack([np.zeros((1, 2), dtype=np.int64), np.cumsum(a, axis=0)])


# ---------- classical float turtle (parametric L-system) --------------------

def float_turtle(rule, K, length):
    """rule = [(turn_before, length_factor), ...] plus a final turn.  Returns
    the vertices of the depth-K curve computed by a float turtle."""
    turns, factors, final = rule
    out = []

    def draw(level, ell, heading):
        if level == 0:
            out.append((ell * math.cos(heading), ell * math.sin(heading)))
            return heading
        for t, f in zip(turns, factors):
            heading += t
            heading = draw(level - 1, ell * f, heading)
        return heading + final
    draw(K, length, 0.0)
    xs, ys = [0.0], [0.0]
    for dx, dy in out:
        xs.append(xs[-1] + dx)
        ys.append(ys[-1] + dy)
    return xs, ys


# ---------- generators --------------------------------------------------------

P = 8
E3 = 3 ** P
L = E3 // 3
H3 = math.sqrt(3) / 2
KOCH60 = [(0, 0), (L, 0), (rnd(Fraction(3 * L, 2)), round(L * H3)), (2 * L, 0), (E3, 0)]
KOCH60_RULE = ([0.0, math.pi / 3, -2 * math.pi / 3, math.pi / 3], [1 / 3] * 4, 0.0)

R_INC = 1 / math.sqrt(3)                 # length ratio, irrational
TH = 1.0                                 # 1 radian, incommensurate with pi
MID = 1 - 2 * R_INC * math.cos(TH)
E2 = 2 ** 10
_p1 = (round(E2 * R_INC * math.cos(TH)), round(E2 * R_INC * math.sin(TH)))
INCOMM = [(0, 0), _p1, (E2 - _p1[0], _p1[1]), (E2, 0)]
INCOMM_RULE = ([TH, -TH, -TH], [R_INC, MID, R_INC], TH)

QUAD = [(3 ** (P - 1) * x, 3 ** (P - 1) * y)
        for x, y in [(0, 0), (1, 0), (1, 1), (2, 1), (2, 0), (3, 0)]]


def block_ends(gen, K):
    """Indices in the depth-K word where the expansions of the depth-1 letters end."""
    sigma = make_sigma(gen)
    size = {}

    def n(v, k):                                        # letters of sigma^k(v), memoised
        if k == 0:
            return 1
        if (v, k) not in size:
            size[v, k] = sum(n(u, k - 1) for u in sigma(v))
        return size[v, k]
    out, i = [], 0
    for v in sigma(gen[-1]):
        i += n(v, K - 1)
        out.append(i)
    return out


def part1():
    print("1. Closure: exact on the lattice, drift in floats")
    for name, gen, rule, K in (("Koch 60 deg snapped, e = (3^8, 0)", KOCH60, KOCH60_RULE, 8),
                               ("1 rad, r = 1/sqrt3, e = (2^10, 0)", INCOMM, INCOMM_RULE, 9)):
        e = gen[-1]
        words = iterate(gen, K)
        for w in words:                                 # word sums to the axiom, every depth
            assert (sum(v[0] for v in w), sum(v[1] for v in w)) == e
        pa = path(words[-1])
        assert tuple(map(int, pa[0])) == (0, 0) and tuple(map(int, pa[-1])) == e
        # the depth-K path passes exactly through the depth-1 vertices (shared vertices)
        verts1 = [tuple(map(int, x)) for x in path(words[1])[1:]]
        assert [tuple(map(int, pa[i])) for i in block_ends(gen, K)] == verts1
        # classical float turtle on the unsnapped generator
        xs, ys = float_turtle(rule, K, float(e[0]))
        err = math.hypot(xs[-1] - e[0], ys[-1] - e[1])
        assert err > 0.0
        # the same vertex along two branches: depth-1 turtle vs depth-K turtle
        x1, y1 = float_turtle(rule, 1, float(e[0]))
        m = len(rule[0])
        diff = [(j, xs[j * m ** (K - 1)] - x1[j], ys[j * m ** (K - 1)] - y1[j])
                for j in range(1, m + 1)]
        mism = [j for j, dx, dy in diff if dx != 0.0 or dy != 0.0]
        print(f"   {name}: depth {K}, {len(words[-1])} letters; word sum and path end"
              f" = {e} exactly at every depth")
        print(f"     float turtle end = ({xs[-1]!r}, {ys[-1]!r}), |end - e| = {err:.3e}")
        print("     shared vertex p_j, depth-%d float turtle minus depth-1 float turtle:" % K)
        for j, dx, dy in diff:
            print(f"       p_{j}: ({dx:+.3e}, {dy:+.3e})")
        assert mism, "no float mismatch found"
        print(f"     -> {len(mism)}/{m} shared vertices differ in the low bits;"
              " the lattice path hits them exactly")


def classical_lsystem(axiom, rules, k):
    s = axiom
    for _ in range(k):
        s = "".join(rules.get(ch, ch) for ch in s)
    return s


def part2():
    print("2. Classical case recovered: quadratic Koch, F -> F+F-F-F+F")
    K = P
    words = iterate(QUAD, K)
    units = [(1, 0), (0, 1), (-1, 0), (0, -1)]          # heading h: + is +90 deg
    for k, w in enumerate(words):
        ell = 3 ** (P - k)
        alphabet = set(w)
        assert len(alphabet) <= 4
        assert alphabet <= {(ell * a, ell * b) for a, b in units}
        s = classical_lsystem("F", {"F": "F+F-F-F+F"}, k)
        h, turtle = 0, []
        for ch in s:
            if ch == "F":
                turtle.append((ell * units[h][0], ell * units[h][1]))
            else:
                h = (h + (1 if ch == "+" else -1)) % 4
        assert turtle == w
    print(f"   depths 0..{K}: alphabet = the 4 axis letters of length 3^(P-k) (P = {P}),"
          f" word = classical L-system ({len(words[-1])} letters at depth {K})")


def part3():
    print("3. Alphabet growth for the 60-degree Koch on the square lattice")
    K = P + 1
    words = iterate(KOCH60, K)
    granule = None
    print("   depth  letters  distinct  max |v|^2  min |v|^2")
    for k, w in enumerate(words):
        n2 = [x * x + y * y for x, y in set(w)]
        e2 = sum(v[0] for v in w), sum(v[1] for v in w)
        assert e2 == KOCH60[-1]
        if granule is None and max(n2) <= 2:
            granule = k
        print(f"   {k:5d} {len(w):8d} {len(set(w)):9d} {max(n2):10d} {min(n2):10d}")
    sizes = [len(set(w)) for w in words]
    assert sizes[0] == 1 and max(sizes) > 6           # grows beyond the 6 hexagonal directions
    assert granule is not None
    print(f"   letters reach the granule (|v|^2 <= 2, i.e. unit or diagonal steps) at depth"
          f" {granule}; every depth is exact")
    return words, K


def part4(words, depth):
    print("4. Exact self-contact count of the granular curve (Koch 60 deg snapped)")
    print("   depth  vertices  distinct  repeated visits  at points  immediate reversals")
    reps = {}
    for k in range(depth - 2, depth + 1):
        word = words[k]
        pa = path(word)
        n_v = len(pa)
        distinct_np = len(np.unique(pa, axis=0))
        counts = {}
        for x, y in pa:
            counts[int(x), int(y)] = counts.get((int(x), int(y)), 0) + 1
        assert distinct_np == len(counts)                # two independent exact counts
        repeats = n_v - len(counts)
        assert sum(c - 1 for c in counts.values()) == repeats
        multi = sum(1 for c in counts.values() if c > 1)
        rev = sum(1 for u, v in zip(word, word[1:]) if u[0] + v[0] == 0 and u[1] + v[1] == 0)
        assert rev <= repeats                            # each reversal revisits a vertex
        reps[k] = (repeats, rev)
        print(f"   {k:5d} {n_v:9d} {len(counts):9d} {repeats:16d} {multi:10d} {rev:20d}")
    assert reps[depth - 2][0] == 0                       # above the granule: simple curve
    print(f"   depth {depth - 2}: no self-contact; at the granule (depth {depth - 1}, {depth})"
          " rounding")
    print("   creates back-and-forth spikes and contacts; every number is an exact integer.")
    # the float analogue is decided by a tolerance
    xs, ys = float_turtle(KOCH60_RULE, depth - 2, float(E3))
    fx, fy = np.array(xs), np.array(ys)
    rows = []
    for tol in (0.0, 1e-9, 1e-6, 1e-3, 1.0, 3.0):
        if tol == 0.0:
            d = len({(a, b) for a, b in zip(xs, ys)})
        else:
            d = len(np.unique(np.round(np.stack([fx, fy], 1) / tol).astype(np.int64), axis=0))
        rows.append((tol, len(xs) - d))
    print(f"   float turtle (unsnapped), depth {depth - 2}, 'repeated vertices' on a grid of side tol: "
          + ", ".join(f"tol {t:g}: {r}" for t, r in rows))
    assert rows[-1][1] > 0 and rows[0][1] == 0           # the float answer moves with tol
    print("   (the classical Koch curve is simple, so its true count is 0; the float count")
    print("   agrees for small tol here but is a function of tol, while the lattice count")
    print("   of the granular curve, which snapping makes self-touching, is one integer.)")


def main():
    part1()
    part2()
    words, depth = part3()
    part4(words, depth)
    print("OK 10b_lsystem_exact")


if __name__ == "__main__":
    main()

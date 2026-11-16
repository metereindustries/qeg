# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""14 -- Quantisability of a small network: a count, not a volume.

Classical problem.  "How robust is a trained network to rounding its
weights?" is classically a question about the Lebesgue volume of the
solution region around the weights in R^d (flatness, sharpness), which is
not invariant under reparametrisation, is not computable for d in the
thousands (volume of a non-convex region), and has no exact meaning for
the weights a machine actually stores, which are lattice points.

Granular resolution (QE measure as counting; Chapter 3 thm:faithful,
Chapter 13 Hoeffding remark in sec:prob-expectation).  The weights live on a fine
lattice (spacing 2^-10).  For a coarse granule eps' the quantisability
profile is the exact fraction
    q(eps') = #{fine points w in the coarse cell of theta : w is a solution}
              / #{fine points in that cell},
the cell being snap(theta) + [-eps', eps')^d (half-open, as in QE2).  It is
a ratio of counts; uniform sampling of n fine points estimates it with the
dimension-free Hoeffding interval |q_hat - q| <= sqrt(ln(2/delta)/(2n))
with probability >= 1 - delta, whatever d is.  Two exact tests complement
it: the snapped point snap(theta) itself, and an interval-arithmetic
certificate that the whole cell consists of solutions (then q = 1 exactly).
For an int8 version, all d*8 single-bit faults are enumerated exhaustively.
All network evaluations are exact integer arithmetic.
"""
import math
import numpy as np

S = 2 ** 10                                   # fine lattice: weights are k / S
H = 8                                         # hidden units
g = np.array([-7, -5, -3, -1, 1, 3, 5, 7])    # inputs i/8 on a dyadic grid
X = np.array([(a, b) for a in g for b in g], dtype=np.int64)        # scale 8
Y = np.sign(X[:, 0] * X[:, 1])                # XOR labels


def train(seed=0, steps=4000, lr=0.05):
    rng = np.random.default_rng(seed)
    W1, b1 = rng.normal(0, 1, (H, 2)), np.zeros(H)
    w2, b2 = rng.normal(0, 0.5, H), 0.0
    x = X / 8.0
    for _ in range(steps):                    # logistic loss, full-batch gradient descent
        a = x @ W1.T + b1
        z = np.maximum(a, 0)
        out = z @ w2 + b2
        gout = -Y / (1 + np.exp(Y * out)) / len(Y)
        gz = np.outer(gout, w2) * (a > 0)
        W1 -= lr * gz.T @ x; b1 -= lr * gz.sum(0)
        w2 -= lr * z.T @ gout; b2 -= lr * gout.sum()
    return np.concatenate([W1.ravel(), b1, w2, [b2]])


def unpack(th):                               # integer parameters, batch axis first
    return th[:, :2 * H].reshape(-1, H, 2), th[:, 2 * H:3 * H], th[:, 3 * H:4 * H], th[:, -1]


def solves(th):
    """th: (m, d) integers at scale S. Exact check y_i f(x_i) > 0 for all 64 inputs."""
    W1, b1, w2, b2 = unpack(th)
    a = np.einsum("mhj,nj->mnh", W1, X) + 8 * b1[:, None, :]          # scale 8 S
    out = np.einsum("mnh,mh->mn", np.maximum(a, 0), w2) + 8 * S * b2[:, None]
    return np.all(Y[None, :] * out > 0, axis=1)


def certified(lo, hi):
    """Interval bound: every integer th with lo <= th <= hi solves (sufficient)."""
    W1l, b1l, w2l, b2l = unpack(lo[None]); W1h, b1h, w2h, b2h = unpack(hi[None])
    xp, xn = np.maximum(X, 0), np.minimum(X, 0)
    lin = lambda A, x: np.einsum("mhj,nj->mnh", A, x)[0]
    al = lin(W1l, xp) + lin(W1h, xn) + 8 * b1l           # lower bound of the pre-activation
    ah = lin(W1h, xp) + lin(W1l, xn) + 8 * b1h
    zl, zh = np.maximum(al, 0), np.maximum(ah, 0)                       # z >= 0
    ol = np.minimum(zl * w2l[0], zh * w2l[0]).sum(1) + 8 * S * b2l[0]
    oh = np.maximum(zl * w2h[0], zh * w2h[0]).sum(1) + 8 * S * b2h[0]
    return bool(np.all(np.where(Y > 0, ol, -oh) > 0))


def main():
    theta = np.rint(train() * S).astype(np.int64)                  # snap to the fine lattice
    d = theta.size
    assert solves(theta[None])[0]
    rng = np.random.default_rng(14)
    n, delta = 4000, 1e-3
    t = math.sqrt(math.log(2 / delta) / (2 * n))                   # Hoeffding, no d in it
    print(f"d = {d} weights on the lattice 2^-10; n = {n} samples; CI +-{t:.4f} at 1-{delta}")
    print(f"{'eps*S':>6} {'cell pts':>9} {'q_hat':>7} {'CI':>16} {'snap ok':>8} {'certified':>10}")
    qs = {}
    for r in [1, 4, 16, 64, 128, 256, 512, 1024]:                        # eps' = r / S
        c = 2 * r * np.floor(theta / (2 * r) + 0.5).astype(np.int64)  # snap to coarse lattice
        W = c[None, :] + rng.integers(-r, r, size=(n, d))           # uniform in c + [-r, r)^d
        q = solves(W).mean()
        cert = certified(c - r, c + r - 1)
        if cert:
            assert q == 1.0                                         # certificate => q = 1 exactly
        qs[r] = q
        pts = f"2^{d * (2 * r).bit_length() - d}"
        ci = f"[{max(q - t, 0):.4f}, {min(q + t, 1):.4f}]"
        print(f"{r:6d} {pts:>9} {q:7.4f} {ci} "
              f"{str(bool(solves(c[None])[0])):>8} {str(cert):>10}")
    assert qs[1] == 1.0 and qs[512] < 0.5 and qs[1024] < 0.05
    # int8 with a power-of-two scale: theta = q8 * 2^e, |q8| <= 127; exhaustive bit flips
    e = max(0, math.ceil(math.log2(np.abs(theta).max() / 127)))
    q8 = np.rint(theta / 2 ** e).astype(np.int64)
    assert np.abs(q8).max() <= 127 and solves((q8 * 2 ** e)[None])[0]
    faults = []
    for i in range(d):
        for b in range(8):
            u = (int(q8[i]) & 0xFF) ^ (1 << b)                     # two's complement byte
            w = q8.copy(); w[i] = u - 256 if u >= 128 else u
            faults.append((b, solves((w * 2 ** e)[None])[0]))
    assert len(faults) == 8 * d
    surv = [np.mean([ok for b, ok in faults if b == k]) for k in range(8)]
    print(f"\nint8 (scale 2^{e - 10}): {len(faults)} single-bit faults enumerated; "
          f"surviving fraction by bit:")
    print("  bit " + " ".join(f"{k:5d}" for k in range(8)))
    print("  ok  " + " ".join(f"{s:5.2f}" for s in surv))
    assert surv[0] >= surv[7]                                       # LSB benign, sign bit not
    print("OK 14_quantisability")


if __name__ == "__main__":
    main()

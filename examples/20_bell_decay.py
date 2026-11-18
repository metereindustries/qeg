# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""20 -- Nonlocality, decay and determinism on finite state spaces.

Classical problem.  Bell's theorem, Tsirelson's bound and no-signalling are
usually stated on infinite-dimensional Hilbert spaces and general probability
spaces; the exponential decay law is postulated (or derived only in a
Markovian limit) although it contradicts recurrence and the finite spectrum
of any bounded system; quantum chaos has no positive Lyapunov exponent to
point to.

Granular resolution (Chapter 21, sec:physics-bell).  Everything is finite,
and the script checks:
  * CHSH: the 16 deterministic local strategies give S = +-2 only; random
    stochastic local models stay within |S| <= 2;
  * the singlet on C^2 (x) C^2 with the standard x-z observables gives
    S = 2 sqrt 2; random states and random +-1 observables on C^m (x) C^n
    satisfy |<S>| <= 2 sqrt 2 and S^2 = 4 - [A0,A1] (x) [B0,B1];
  * no-signalling for a random density matrix on C^2 (x) C^3;
  * decay as counting: #{tau >= t} = sum_b (g_b - t)_+ exactly, for the
    regular register x -> x+1 (equal gaps: linear law), for the overflow
    register x -> b x mod p (gap histogram close to geometric), and for an
    exact finite geometric profile (survival 2^-t exactly);
  * recurrence: a time t <= N^d with |U^t psi - psi| <= (2 pi/N)|psi|
    for all psi;
  * linear in the state: exact distance preservation; the Hartree map is not
    additive; three bodies on a ring have Wigner-Dyson level statistics, a
    separable system has Poisson statistics.
Units hbar = a = 1.
"""
import itertools
import math

import numpy as np

rng = np.random.default_rng(20)
SQ2 = math.sqrt(2)


def chsh_local():
    vals = set()
    for a0, a1, b0, b1 in itertools.product([1, -1], repeat=4):
        vals.add(a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1)
    assert vals == {2, -2}
    worst = 0.0
    for _ in range(2000):                      # stochastic local models
        L = 5
        w = rng.random(L); w /= w.sum()
        A = rng.uniform(-1, 1, (2, L)); B = rng.uniform(-1, 1, (2, L))
        E = lambda x, y: np.sum(w * A[x] * B[y])
        S = E(0, 0) + E(0, 1) + E(1, 0) - E(1, 1)
        worst = max(worst, abs(S))
    assert worst <= 2 + 1e-12
    print(f"CHSH: deterministic strategies give S in {sorted(vals)}")
    print(f"      2000 stochastic local models: max |S| = {worst:.4f} <= 2")


def chsh_op(A0, A1, B0, B1):
    return (np.kron(A0, B0) + np.kron(A0, B1) + np.kron(A1, B0)
            - np.kron(A1, B1))


def random_involution(n):
    """Random Hermitian matrix with square 1: U diag(+-1) U*."""
    X = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    U, _ = np.linalg.qr(X)
    s = rng.choice([1, -1], size=n)
    return U @ np.diag(s) @ U.conj().T


def quantum_value():
    Z = np.array([[1, 0], [0, -1]], dtype=complex)
    X = np.array([[0, 1], [1, 0]], dtype=complex)
    B0 = -(Z + X) / SQ2
    B1 = (X - Z) / SQ2
    psi = np.array([0, 1, -1, 0], dtype=complex) / SQ2   # (|01> - |10>)/sqrt 2
    S = chsh_op(Z, X, B0, B1)
    val = np.real(psi.conj() @ S @ psi)
    assert abs(val - 2 * SQ2) < 1e-14
    print(f"\nsinglet: <psi, S psi> = {val:.12f} = 2 sqrt 2 = {2 * SQ2:.12f}")
    best = 0.0
    for m, n in [(2, 2), (2, 3), (3, 4)]:
        for _ in range(300):
            A0, A1 = random_involution(m), random_involution(m)
            C0, C1 = random_involution(n), random_involution(n)
            S = chsh_op(A0, A1, C0, C1)
            K = np.kron(A0 @ A1 - A1 @ A0, C0 @ C1 - C1 @ C0)
            assert np.allclose(S @ S, 4 * np.eye(m * n) - K, atol=1e-11)
            ph = rng.normal(size=m * n) + 1j * rng.normal(size=m * n)
            ph /= np.linalg.norm(ph)
            v = abs(ph.conj() @ S @ ph)
            assert v <= 2 * SQ2 + 1e-12
            best = max(best, np.max(np.abs(np.linalg.eigvalsh(S))))
    assert best <= 2 * SQ2 + 1e-12
    print("Tsirelson: S^2 = 4 - [A0,A1](x)[B0,B1] on C^2(x)C^2, C^2(x)C^3,"
          " C^3(x)C^4")
    print(f"           max |eig S| = {best:.6f} <= 2 sqrt 2 = {2 * SQ2:.6f}")


def projective(n, k):
    """Random projective measurement on C^n with k outcomes."""
    X = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    U, _ = np.linalg.qr(X)
    cuts = np.sort(rng.choice(np.arange(1, n), size=k - 1, replace=False))
    blocks = np.split(np.arange(n), cuts)
    return [U[:, b] @ U[:, b].conj().T for b in blocks]


def no_signalling():
    m, n = 2, 3
    G = rng.normal(size=(m * n, m * n)) + 1j * rng.normal(size=(m * n, m * n))
    rho = G @ G.conj().T; rho /= np.trace(rho)
    P = projective(m, 2); Q = projective(n, 2); Q2 = projective(n, 3)
    gap = 0.0
    for Pa in P:
        marg = np.trace(rho @ np.kron(Pa, np.eye(n)))
        s1 = sum(np.trace(rho @ np.kron(Pa, Qb)) for Qb in Q)
        s2 = sum(np.trace(rho @ np.kron(Pa, Qb)) for Qb in Q2)
        gap = max(gap, abs(s1 - marg), abs(s2 - marg))
        for Qb in Q + Q2:
            pr = np.trace(rho @ np.kron(Pa, Qb))
            assert pr.real >= -1e-14 and abs(pr.imag) < 1e-14
    total = sum(np.trace(rho @ np.kron(Pa, Qb)) for Pa in P for Qb in Q)
    assert gap < 1e-14 and abs(total - 1) < 1e-14
    print("\nno-signalling on C^2(x)C^3:")
    print(f"  |sum_b p(a,b|Q) - sum_b p(a,b|Q')| <= {gap:.1e}")
    print(f"  probabilities >= 0, total {total.real:.15f}")


def decay_counts(perm, A):
    """tau(x) = first t >= 0 with perm^t x in A; gaps = backward returns."""
    M = len(perm)
    inA = np.zeros(M, bool); inA[list(A)] = True
    inv = np.empty(M, int); inv[perm] = np.arange(M)
    tau = np.empty(M, int)
    for x in range(M):
        t, y = 0, x
        while not inA[y]:
            y = perm[y]; t += 1
        tau[x] = t
    gaps = []
    for b in A:
        s, y = 1, inv[b]
        while not inA[y]:
            y = inv[y]; s += 1
        gaps.append(s)
    return tau, np.array(gaps)


def check_gap_formula(tau, gaps, tmax):
    for t in range(tmax):
        assert np.sum(tau >= t) == np.sum(np.maximum(gaps - t, 0))
    assert gaps.sum() == len(tau)                                  # Kac
    assert 2 * tau.sum() == np.sum(gaps * (gaps - 1))   # mean decay time


def decay():
    # regular register: rotation, equally spaced decay states
    M, g = 1200, 40
    perm = (np.arange(M) + 1) % M
    A = list(range(0, M, g))
    tau, gaps = decay_counts(perm, A)
    check_gap_formula(tau, gaps, 2 * g)
    S = [np.sum(tau >= t) / M for t in range(g + 1)]
    assert all(abs(S[t] - max(0, 1 - t / g)) < 1e-15 for t in range(g + 1))
    print(f"\nregular register x -> x+1 mod {M}, "
          f"{len(A)} equally spaced decay states:")
    print(f"  S(t) = (1 - t/{g})_+ exactly (linear, not exponential):")
    print(f"  S(10) = {S[10]:.4f}, S(20) = {S[20]:.4f}, S(40) = {S[40]:.4f}")

    # overflow register: x -> b x mod p on (Z/p)^*, b a primitive root,
    # A = an interval
    p, k = 100003, 500
    q = 1 - k / (p - 1)
    for b, c, generic in [(5, p // 3, True), (2, 1, False)]:
        order = next(d for d in range(1, p)
                     if (p - 1) % d == 0 and pow(b, d, p) == 1)
        assert order == p - 1                  # one cycle of length p-1
        perm = (b * np.arange(1, p)) % p - 1   # state x has index x-1
        A = list(range(c - 1, c - 1 + k))      # states c..c+k-1
        tau, gaps = decay_counts(perm, A)
        check_gap_formula(tau, gaps, 40)
        print(f"overflow register x -> {b}x mod {p} (one cycle of {p - 1}),")
        print(f"  A = {{{c}..{c + k - 1}}}:")
        print(f"  exact gap formula holds, mean gap {gaps.mean():.0f}"
          " = (p-1)/k")
        ts = [100, 200, 400, 800, 1600]
        St = [np.sum(tau >= t) / (p - 1) for t in ts]
        print("  t:     " + " ".join(f"{t:8d}" for t in ts))
        print("  S(t):  " + " ".join(f"{v:8.4f}" for v in St))
        print("  q^t:   " + " ".join(f"{q ** t:8.4f}" for t in ts))
        dev = max(abs(v - q ** t) for v, t in zip(St, ts))
        edges = np.arange(1, 1201, 100)
        hist = np.array([np.sum((gaps >= lo) & (gaps < lo + 100))
                         for lo in edges])
        geo = np.array([k * (q ** (lo - 1) - q ** (lo + 99)) for lo in edges])
        chi2 = np.sum((hist - geo) ** 2 / geo)
        print(f"  gap histogram vs k p q^(g-1), {len(edges)} bins of 100: "
              f"chi^2 = {chi2:.1f}")
        print(f"  max |S(t) - q^t| = {dev:.4f}")
        if generic:
            assert dev < 0.02 and chi2 < 25
        else:   # A = {1..k} is nearly closed under x -> 2x: clustered gaps
            assert dev > 0.1 and np.sum(gaps == 1) > 200
            print(f"  ({np.sum(gaps == 1)} gaps of length 1: "
                  "the decay set is nearly invariant)")

    # exact finite geometric profile:
    # 2^(T-j) gaps of length j (1 <= j <= T), and one of length T+2
    T = 9
    gl = [j for j in range(1, T + 1) for _ in range(2 ** (T - j))] + [T + 2]
    rng.shuffle(gl)
    M = sum(gl); assert M == 2 ** (T + 1) and len(gl) == 2 ** T
    pos = np.cumsum(gl) % M
    perm = (np.arange(M) + 1) % M
    tau, gaps = decay_counts(perm, list(pos))
    check_gap_formula(tau, gaps, T + 3)
    for t in range(T + 2):
        assert np.sum(tau >= t) == 2 ** (T + 1 - t)
    print(f"exact geometric profile on {M} states:")
    print(f"  #{{tau >= t}} = 2^({T + 1}-t) for 0 <= t <= {T + 1}; "
          "half-life exactly 1 step")


def cayley(H, tau=1.0):
    A = tau * H / 2
    I = np.eye(len(H))
    return (I - 1j * A) @ np.linalg.inv(I + 1j * A)


def recurrence():
    d, N = 4, 8
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    H = (X + X.conj().T) / 2
    U = cayley(H)
    lam = np.linalg.eigvalsh(H / 2)
    u = (1 - 1j * lam) / (1 + 1j * lam)
    assert np.allclose(np.sort_complex(np.linalg.eigvals(U)),
                       np.sort_complex(u), atol=1e-12)
    bound = 2 * math.pi / N
    t = next(t for t in range(1, N ** d + 1)
             if np.max(np.abs(u ** t - 1)) <= bound)
    Ut = np.linalg.matrix_power(U, t)
    worst = 0.0
    for _ in range(200):
        psi = rng.normal(size=d) + 1j * rng.normal(size=d)
        err = np.linalg.norm(Ut @ psi - psi) / np.linalg.norm(psi)
        worst = max(worst, err)
        amp = abs(psi.conj() @ Ut @ psi - np.linalg.norm(psi) ** 2)
        assert amp <= bound * np.linalg.norm(psi) ** 2 + 1e-12
    assert worst <= bound + 1e-12
    print(f"\nrecurrence, d = {d}, N = {N}: t = {t} <= N^d = {N ** d}")
    print(f"  max |U^t psi - psi|/|psi| = {worst:.4f} <= 2 pi/N = {bound:.4f}")


def ratio_stat(E):
    E = np.sort(E)
    n = len(E)
    E = E[n // 4: 3 * n // 4]
    s = np.diff(E)
    s = s[s > 1e-10]
    r = np.minimum(s[1:], s[:-1]) / np.maximum(s[1:], s[:-1])
    return r.mean()


def three_body(L, t, V12, V13, V23, theta):
    """Sector e^{i theta x3} phi(x1 - x3, x2 - x3), three particles on Z/L."""
    n = L * L
    H = np.zeros((n, n), complex)
    idx = lambda r1, r2: (r1 % L) * L + (r2 % L)
    for r1 in range(L):
        for r2 in range(L):
            i = idx(r1, r2)
            H[i, i] += (2 * (t[0] + t[1] + t[2]) + V12[(r1 - r2) % L]
                        + V13[r1] + V23[r2])
            for s in (1, -1):
                H[i, idx(r1 + s, r2)] -= t[0]
                H[i, idx(r1, r2 + s)] -= t[1]
                H[i, idx(r1 - s, r2 - s)] -= t[2] * np.exp(1j * s * theta)
    return H


def linear_vs_chaotic():
    # exact isometry of many-body evolution
    H = three_body(6, (0.5, 0.35, 0.2), rng.normal(size=6), rng.normal(size=6),
                   rng.normal(size=6), 2 * math.pi / 6)
    U = cayley(H, 0.3)
    psi = rng.normal(size=36) + 1j * rng.normal(size=36)
    phi = psi + 1e-3 * (rng.normal(size=36) + 1j * rng.normal(size=36))
    d0 = np.linalg.norm(psi - phi)
    for _ in range(1000):
        psi, phi = U @ psi, U @ phi
    rel = abs(np.linalg.norm(psi - phi) / d0 - 1)
    assert rel < 1e-9
    print("\nthree-body Cayley evolution, 1000 steps:")
    print(f"  |U^t psi - U^t phi| / |psi - phi| - 1 = {rel:.1e}")
    print("  (Lyapunov exponent 0)")
    # Hartree map is not additive
    Lh = 5
    E = np.eye(Lh)
    h0 = 2 * E - np.roll(E, 1, 0) - np.roll(E, -1, 0)
    Vp = np.array([1.0, 0.3, 0.1, 0.1, 0.3])
    mf = lambda f: np.array([sum(Vp[(x - y) % Lh] * abs(f[y]) ** 2
                                 for y in range(Lh))
                             for x in range(Lh)])
    F = lambda f: h0 @ f + mf(f) * f
    delta = np.zeros(Lh, complex); delta[0] = 1
    diff = F(2 * delta) - 2 * F(delta)
    assert abs(diff[0] - 6 * Vp[0]) < 1e-14
    print(f"Hartree field: F(d + d) - 2F(d) at x = {diff[0].real:.1f} = 6 V(0)")
    print("  (cubic, not additive)")
    # level statistics: separable versus interacting three bodies
    L = 24
    theta = 2 * math.pi * 5 / L
    r = np.minimum(np.arange(L), L - np.arange(L))
    Vy = lambda c: -2.0 * c / (r + 1.0)        # screened pair potentials
    zero = np.zeros(L)
    # separable: heavy third body (t3 = 0) and no force between bodies 1, 2
    Hsep = three_body(L, (0.5, 0.37, 0.0), zero, Vy(0.7), Vy(-0.6), theta)
    Hint = three_body(L, (0.5, 0.37, 0.23), Vy(1.0), Vy(0.7), Vy(-0.6), theta)
    r_sep = ratio_stat(np.linalg.eigvalsh(Hsep))
    r_int = ratio_stat(np.linalg.eigvalsh(Hint))
    print(f"level-spacing ratio <r>, middle half of {L * L} levels "
          "of one momentum sector:")
    print(f"  separable (heavy 3rd body, no 1-2 force) {r_sep:.3f}  Poisson 0.386")
    print(f"  three interacting bodies                 {r_int:.3f}  GOE 0.536")
    assert r_sep < 0.45 and r_int > 0.5


def main():
    chsh_local()
    quantum_value()
    no_signalling()
    decay()
    recurrence()
    linear_vs_chaotic()
    print("OK 20_bell_decay")


if __name__ == "__main__":
    main()

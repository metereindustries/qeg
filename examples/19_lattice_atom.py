# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""19 -- The atom on the lattice: two point-spheres, the reduced mass, collapse.

Classical problem.  The continuum hydrogen Hamiltonian -hbar^2/2m Lap_e
- hbar^2/2M Lap_N - Ze^2/(4 pi eps0 |x_e - x_N|) is unbounded above, its
potential is singular at coincidence, and its lower bound needs Hardy's or
Kato's inequality.  Position eigenstates are not states, a sharp position
measurement costs infinite energy, and the centre-of-mass separation rests
on exact Galilean invariance.

Granular resolution (Chapter 21, sec:physics-atom).  Electron and nucleus
are two point-spheres on a ring of N sites.  The script checks:
  * exact two-body reduction: the spectrum of the N^2 x N^2 two-body matrix is
    the union over K of the spectra of the N x N relative matrices H_theta
    (theta = 2 pi K/N), whose hopping is t_e + t_N e^{-+i theta};
  * at theta = 0 the relative matrix is the one-body matrix with hopping
    hbar^2/(2 mu a^2): the reduced mass mu = mM/(m+M) appears exactly;
  * the ground energy of each total-momentum sector depends on theta, the
    dependence vanishes for an infinitely heavy nucleus (t_N = 0), and
    |t_e + t_N e^{i theta}|^2 = (t_e+t_N)^2 - 4 t_e t_N sin^2(theta/2);
  * the Cayley step is unitary, and the Zeno bound
    |(PU)^n psi|^2 >= (1 - x^2)^n |psi|^2, x = tau |H| / hbar, holds;
  * GRW collapse: sum_k L_k H0 L_k = H0 with hopping x c, c = sum sqrt(g_j g_j+1);
    for a Gaussian of width r_C >> a the injected energy per collapse is
    hbar^2/(4 m r_C^2), independent of the granule; for g = delta, c = 0.
Units hbar = a = 1 (a = lattice spacing = 2 eps).
"""
import numpy as np


def ring_lap(N, t):
    """t (2 - T - T^-1) on the ring Z/N."""
    H = 2 * t * np.eye(N)
    for x in range(N):
        H[x, (x + 1) % N] -= t
        H[x, (x - 1) % N] -= t
    return H


def two_body(N, te, tN, V):
    """H on psi(x_e, x_N), index x_e * N + x_N."""
    H = np.kron(ring_lap(N, te), np.eye(N)) + np.kron(np.eye(N), ring_lap(N, tN))
    for xe in range(N):
        for xN in range(N):
            i = xe * N + xN
            H[i, i] += V[(xe - xN) % N]
    return H


def relative(N, te, tN, V, theta):
    """H_theta phi(r) = 2(te+tN) phi(r) - (te + tN e^{-i th}) phi(r+1)
    - (te + tN e^{i th}) phi(r-1) + V(r) phi(r)."""
    w = np.exp(1j * theta)
    H = np.diag(2 * (te + tN) + V.astype(complex))
    for r in range(N):
        H[r, (r + 1) % N] -= te + tN / w
        H[r, (r - 1) % N] -= te + tN * w
    return H


def cayley(H, tau):
    A = tau * H / 2
    I = np.eye(len(H))
    return (I - 1j * A) @ np.linalg.inv(I + 1j * A)


def main():
    rng = np.random.default_rng(19)
    N, m, M = 24, 1.0, 5.0                     # light "nucleus" to make effects visible
    te, tN = 1 / (2 * m), 1 / (2 * M)
    r = np.minimum(np.arange(N), N - np.arange(N))
    V = -2.0 / (r + 1.0)                       # attractive pair potential, finite at r = 0

    # exact two-body reduction
    E_full = np.sort(np.linalg.eigvalsh(two_body(N, te, tN, V)))
    E_rel = np.sort(np.concatenate([np.linalg.eigvalsh(relative(N, te, tN, V, 2 * np.pi * K / N))
                                    for K in range(N)]))
    assert np.max(np.abs(E_full - E_rel)) < 1e-10
    print(f"two-body spectrum ({N * N} levels) = union of {N} relative spectra: "
          f"max diff {np.max(np.abs(E_full - E_rel)):.1e}")

    # reduced mass at theta = 0
    mu = m * M / (m + M)
    assert abs(te + tN - 1 / (2 * mu)) < 1e-15
    assert np.allclose(relative(N, te, tN, V, 0.0), ring_lap(N, 1 / (2 * mu)) + np.diag(V))
    print(f"theta = 0: hopping t_e + t_N = {te + tN:.6f} = 1/(2 mu), mu = {mu:.6f}")

    # internal ground energy versus total momentum
    print(f"\n{'K':>3} {'theta':>7} {'E0(theta)':>11} {'E0 - E0(0)':>11} "
          f"{'|t_e+t_N e^it|':>15} {'t_N = 0':>10}")
    E0 = []
    for K in range(N // 2 + 1):
        th = 2 * np.pi * K / N
        e0 = np.linalg.eigvalsh(relative(N, te, tN, V, th))[0]
        e_heavy = np.linalg.eigvalsh(relative(N, te, 0.0, V, th))[0]
        hop = abs(te + tN * np.exp(1j * th))
        assert abs(hop ** 2 - ((te + tN) ** 2 - 4 * te * tN * np.sin(th / 2) ** 2)) < 1e-14
        E0.append((e0, e_heavy))
        if K in (0, 1, 2, 3, 6, 12):
            print(f"{K:3d} {th:7.4f} {e0:11.6f} {e0 - E0[0][0]:11.2e} {hop:15.6f} {e_heavy:10.6f}")
    e0s = [e for e, _ in E0]
    assert all(e0s[k] < e0s[k + 1] for k in range(len(e0s) - 1))     # binding varies with theta
    assert max(abs(h - E0[0][1]) for _, h in E0) < 1e-12              # heavy nucleus: no theta
    print("sector ground energy rises with |theta|; with t_N = 0 it is theta-independent")

    # Cayley unitarity and the Zeno bound
    n8 = 8
    r8 = np.minimum(np.arange(n8), n8 - np.arange(n8))
    H = two_body(n8, te, tN, -2.0 / (r8 + 1.0))       # 64 x 64 two-body matrix
    hnorm = np.max(np.abs(np.linalg.eigvalsh(H)))
    tau = 0.05 / hnorm
    U = cayley(H, tau)
    assert np.allclose(U.conj().T @ U, np.eye(len(H)), atol=1e-12)
    x = tau * hnorm
    P = np.zeros(len(H)); P[:len(H) // 2] = 1
    psi = rng.normal(size=len(H)) + 1j * rng.normal(size=len(H)); psi *= P
    psi /= np.linalg.norm(psi)
    phi = psi.copy()
    for n in range(1, 101):
        phi = P * (U @ phi)
        assert np.linalg.norm(phi) ** 2 >= (1 - x ** 2) ** n - 1e-12
    print(f"\nCayley step unitary; Zeno: after 100 steps |(PU)^n psi|^2 = "
          f"{np.linalg.norm(phi) ** 2:.6f} >= (1-x^2)^100 = {(1 - x ** 2) ** 100:.6f}")

    # GRW collapse on a ring of L sites
    L, mass = 400, 1.0
    t = 1 / (2 * mass)
    H0 = ring_lap(L, t)
    print(f"\n{'r_C/a':>6} {'1 - c':>10} {'dE/collapse':>12} {'hbar^2/4mr_C^2':>15}")
    for w in [0, 5, 10, 20]:
        j = np.arange(L); d = np.minimum(j, L - j)
        g = np.exp(-(d / w) ** 2) if w > 0 else (d == 0).astype(float)
        g /= g.sum()
        c = np.sum(np.sqrt(g * np.roll(g, -1)))
        S = np.zeros((L, L))
        for k in range(L):
            Lk = np.diag(np.sqrt(np.roll(g, k)))
            S += Lk @ H0 @ Lk
        Hc = 2 * t * np.eye(L) - c * (2 * t * np.eye(L) - H0)
        assert np.allclose(S, Hc, atol=1e-12)                # sandwich identity, exact
        assert 0 <= c <= 1
        k0 = 2 * np.pi / L                                   # a slow state: lowest plane wave
        psi = np.exp(1j * k0 * j) / np.sqrt(L)
        dE = np.real(psi.conj() @ (S - H0) @ psi)
        assert abs(dE) <= (1 - c) * 2 * t + 1e-12
        if w == 0:
            assert c == 0
            print(f"{'delta':>6} {1 - c:10.6f} {dE:12.6f} {'-':>15}   (= hbar^2/(m a^2) cos k)")
        else:
            ref = 1 / (4 * mass * w ** 2)
            assert abs(dE / ref - 1) < 0.01
            print(f"{w:6d} {1 - c:10.3e} {dE:12.4e} {ref:15.4e}")
    print("energy per collapse -> hbar^2/(4 m r_C^2), independent of the granule a")
    print("OK 19_lattice_atom")


if __name__ == "__main__":
    main()

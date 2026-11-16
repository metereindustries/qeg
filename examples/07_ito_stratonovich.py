# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.

"""07 -- Ito versus Stratonovich on the Anderson walk.

Classical problem.  The "integral" of W dW along a Brownian path is not a
Riemann-Stieltjes integral: Brownian paths have infinite variation, and the
limit of the Riemann sums depends on where each cell is sampled (left point:
(W_T^2 - T)/2, Ito; midpoint/trapezoid: W_T^2/2, Stratonovich).  A model
"dX = b(X) dW" written without a convention is ill-posed (the two readings
differ by the noise-induced drift b b'/2), and the convention is external
information that the continuum equation does not carry.

Granular resolution (Chapter 15: thm:ito-exact, thm:stoch-ito-strat,
thm:stoch-WdW).  On the time lattice t_k = k tau the Anderson walk
W(t_k) = sum_{j<k} xi_j sqrt(tau), xi = +-1, satisfies (dW)^2 = tau on every
path, exactly, and on every path
    sum W_k dW_k                        = W_T^2/2 - T/2      (Ito, [t_k, t_k+1))
    sum (W_k + W_{k+1})/2 dW_k          = W_T^2/2            (Stratonovich)
    sum ((1-l) W_k + l W_{k+1}) dW_k    = W_T^2/2 + (l - 1/2) T.
The difference T/2 is (1/2) sum (dW)^2: the openness bit of each time cell
([t_k, t_k+1) versus (t_k, t_k+1]) summed over n cells.
All arithmetic is exact (Fractions); sqrt(tau) = s is a lattice step.
"""
from fractions import Fraction as F
from itertools import product
import random


def sums(xi, s, lam):
    W = [F(0)]
    for x in xi:
        W.append(W[-1] + x * s)
    dW = [W[k + 1] - W[k] for k in range(len(xi))]
    ito = sum(W[k] * dW[k] for k in range(len(xi)))
    strat = sum((W[k] + W[k + 1]) / 2 * dW[k] for k in range(len(xi)))
    lsum = sum(((1 - lam) * W[k] + lam * W[k + 1]) * dW[k] for k in range(len(xi)))
    return W, dW, ito, strat, lsum


def check_path(xi, s, lam):
    tau, T = s * s, len(xi) * s * s
    W, dW, ito, strat, lsum = sums(xi, s, lam)
    assert all(d * d == tau for d in dW)                       # thm:ito-exact
    assert ito == W[-1] ** 2 / 2 - T / 2                        # Ito
    assert strat == W[-1] ** 2 / 2                              # Stratonovich
    assert lsum == W[-1] ** 2 / 2 + (lam - F(1, 2)) * T         # lambda-sum
    assert strat - ito == sum(d * d for d in dW) / 2 == T / 2  # openness of n cells
    return W[-1], ito, strat


def main():
    s = F(1, 2 ** 6)                       # sqrt(tau) = 2eps; tau = 2^-12
    lam = F(1, 3)
    # every path of n = 12 steps: 4096 paths, exhaustively
    n = 12
    tot_ito = tot_strat = F(0)
    for xi in product((1, -1), repeat=n):
        _, ito, strat = check_path(xi, s, lam)
        tot_ito += ito
        tot_strat += strat
    T = n * s * s
    assert tot_ito / 2 ** n == 0                               # Ito sums are centred
    assert tot_strat / 2 ** n == T / 2                         # Stratonovich has drift T/2
    print(f"all 2^{n} paths, tau = {s * s}: (dW)^2 = tau, identities exact; "
          f"E[Ito] = 0, E[Strat] = T/2 = {T / 2}")
    # long random paths, T = 1
    rng = random.Random(20261017)
    n = 2 ** 12
    print(f"\n{'path':>4} {'W_T':>9} {'Ito sum':>12} {'(W^2-T)/2':>12} "
          f"{'Strat sum':>12} {'S - I':>6}")
    for p in range(5):
        xi = [rng.choice((1, -1)) for _ in range(n)]
        WT, ito, strat = check_path(xi, s, lam)
        print(f"{p:4d} {float(WT):9.5f} {float(ito):12.6f} "
              f"{float((WT ** 2 - 1) / 2):12.6f} {float(strat):12.6f} {str(strat - ito):>6}")
    print("Ito - Strat = -T/2 exactly on every path (T = n tau = 1).")
    print("OK 07_ito_stratonovich")


if __name__ == "__main__":
    main()

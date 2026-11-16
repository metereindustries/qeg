# SPDX-License-Identifier: MIT
# Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
# Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
#   This work is derivative of the Quasi-Euclidean Granular Geometry book
#   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
#   All rights reserved
# See LICENSE.md and NOTICE.
"""Exhaustive check of a small circuit for the 3-SAT switchboard on n = 4 variables.

The switchboard has N = 8*C(4,3) = 32 switches, one per 3-clause on four variables; the
function is 1 when the switched-on clauses are satisfiable.  The script

  * builds the pairing circuit: for each pair of assignments differing in the last
    variable, (P or Q) and (P or R) = P or (Q and R), with P the disjunction of the clauses
    falsified by both;
  * rewrites it over {AND, NOT} (OR(a, b) = NOT(AND(NOT a, NOT b)), double negations
    removed, NOT gates shared);
  * checks both circuits against the definition of satisfiability on all 2^32 switchboards,
    20 switches at a time in parallel bit vectors (numpy).

Chapter 19 (ch:gcc). Needs Python 3 and numpy; runs in about ten seconds.  Every printed claim is asserted.
"""
import itertools
import numpy as np

n = 4
CL = [(T, s) for T in itertools.combinations(range(n), 3) for s in itertools.product((0, 1), repeat=3)]
N = len(CL)
FALS = [[x for x in range(1 << n) if all(((x >> T[j]) & 1) == s[j] for j in range(3))] for T, s in CL]
BY_X = [[i for i in range(N) if x in FALS[i]] for x in range(1 << n)]


def pairing_circuit():
    gates = []

    def g(op, a, b=None):
        gates.append((op, a, b))
        return N + len(gates) - 1

    def big(op, ws):
        w = ws[0]
        for v in ws[1:]:
            w = g(op, w, v)
        return w
    pairs = []
    for x in range(1 << n):
        if x >> (n - 1) & 1:
            continue
        y = x | (1 << (n - 1))
        shared = sorted(set(BY_X[x]) & set(BY_X[y]))
        ox = [i for i in BY_X[x] if i not in shared]
        oy = [i for i in BY_X[y] if i not in shared]
        inner = g("and", big("or", ox), big("or", oy))
        pairs.append(g("or", big("or", shared), inner) if shared else inner)
    out = g("not", big("and", pairs))
    return gates, out


def to_and_not(gates, out):
    """Rewrite over {AND, NOT}: wires are (index, negated) pairs; NOTs are materialised once."""
    new, lit, notw = [], {}, {}

    def emit(op, a, b=None):
        new.append((op, a, b))
        return N + len(new) - 1

    def wire(l):                       # materialise a literal as a wire
        w, neg = l
        if not neg:
            return w
        if w not in notw:
            notw[w] = emit("not", w)
        return notw[w]
    for i in range(N):
        lit[i] = (i, False)
    for k, (op, a, b) in enumerate(gates):
        idx = N + k
        if op == "not":
            w, neg = lit[a]
            lit[idx] = (w, not neg)
        elif op == "and":
            lit[idx] = (emit("and", wire(lit[a]), wire(lit[b])), False)
        else:                          # a or b = not(not a and not b)
            na, nb = (lit[a][0], not lit[a][1]), (lit[b][0], not lit[b][1])
            lit[idx] = (emit("and", wire(na), wire(nb)), True)
    return new, wire(lit[out])


def evaluate(gates, inputs):
    w = list(inputs)
    for op, a, b in gates:
        w.append(w[a] & w[b] if op == "and" else w[a] | w[b] if op == "or" else ~w[a])
    return w


def main():
    gates, out = pairing_circuit()
    an, out2 = to_and_not(gates, out)
    count = lambda gs, op: sum(1 for g in gs if g[0] == op)
    print(f"pairing circuit: {len(gates)} gates ({count(gates, 'and')} AND, {count(gates, 'or')} OR,"
          f" {count(gates, 'not')} NOT)")
    print(f"over {{AND, NOT}}: {len(an)} gates ({count(an, 'and')} AND, {count(an, 'not')} NOT)")
    S = 20                                   # switches 0..19 in parallel, 20..31 enumerated
    pos = np.arange(1 << S, dtype=np.uint32)
    par = [np.packbits(((pos >> j) & 1).astype(bool)) for j in range(S)]
    ones = np.full_like(par[0], 0xFF)
    zero = np.zeros_like(par[0])
    nsat = 0
    for hi in range(1 << (N - S)):
        inputs = par + [ones if (hi >> (j - S)) & 1 else zero for j in range(S, N)]
        unsat = ones.copy()                  # definition: every assignment is blocked
        for x in range(1 << n):
            blk = zero.copy()
            for i in BY_X[x]:
                blk |= inputs[i]
            unsat &= blk
        sat = ~unsat
        w1 = evaluate(gates, inputs)
        w2 = evaluate(an, inputs)
        assert np.array_equal(w1[out], sat) and np.array_equal(w2[out2], sat), hi
        nsat += int(np.unpackbits(sat).sum())
    print(f"both circuits agree with satisfiability on all 2^32 switchboards ({nsat} satisfiable)")
    assert nsat == 2573599545


if __name__ == "__main__":
    main()

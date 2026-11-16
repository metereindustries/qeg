# Quasi-Euclidean Granular Geometry

*Calculus, analysis, geometry, topology, probability, information and dynamics on
the axiom that a point is a sphere, small enough.*

> **Axiom.** A point is a sphere in ℝⁿ of radius ε, where ε is, by definition,
> smaller than any other quantity under consideration.

By Alfredo Metere. Copyright 2026 Metere Industries, Inc.

Euclid defined a point as "that which has no part". This book replaces that
definition with the one above and rebuilds calculus, real analysis, measure
theory, geometry, topology, probability, statistics, stochastic calculus,
information theory, nonlinear dynamics, computational complexity and physics on
that basis. ε is part of the domain of existence and has a definite scale: it is
the resolution of the space, not a parameter sent to zero. The classical theory
is recovered from the granular one as a shadow.

## Contents of this repository

| Path | What it is |
|---|---|
| `Quasi-Euclidean-Granular-Geometry.pdf` | The book |
| `chapters-pdf/` | One PDF per chapter and appendix |
| `lean/` | The Lean 4 formalisation: every theorem of the book, checked by the Lean kernel |
| `examples/` | Python scripts of the computational companion; each asserts every claim it prints |

## Checking the proofs

Install Lean through [elan](https://github.com/leanprover/elan), then

    cd lean
    lake exe cache get      # prebuilt Mathlib
    lake build QuasiEuclidean

The build uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Each theorem in the book names the Lean constants that prove it.

## Running the examples

    python3 examples/run_all.py        # Python 3 with numpy

`run_all.py` exits non-zero if any claim fails.

## Authorship

The axiom, the core ideas, the resolution of the core issues in keeping the
axiom consistent, and the architecture of the book are the author's. The text,
figures, Lean proofs, Python programs and tools were written by Anthropic's
Claude models under the author's heavy direction; the author is responsible
for the whole. The Lean statements are the authoritative form of each result.
This is a working edition, updated from time to time.

## Licence

The book and its PDFs are licensed under CC BY 4.0, and the code (`lean/`,
`examples/`) under the MIT licence; see [`LICENSE.md`](LICENSE.md). Any
derivative work must display the notice in [`NOTICE`](NOTICE).

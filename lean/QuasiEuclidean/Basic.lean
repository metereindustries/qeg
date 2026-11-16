-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import Mathlib

/-!
# Quasi-Euclidean geometry: core definitions

The founding axiom of the book: *a point is a sphere of radius `ε`, where `ε`
is smaller than any other quantity under consideration*.

## Modelling choices

* Neighbouring point-spheres touch, so their centres form the lattice
  `2εℤ`.  A lattice point is described by its integer index `k : ℤ`
  (centre `2 ε k`); in `n` dimensions by `k : Fin n → ℤ`.
* A configuration is a finite set of indices (`Finset ℤ`).  In the book the
  ambient lattice is hyperfinite; every internal set is hyperfinite, and the
  combinatorial identities proved here are identities about finite sets,
  valid for every `ε > 0`.
* We work over an arbitrary linearly ordered field `K` and an arbitrary
  `ε > 0`.  Instantiating `K := ℝ*` (Mathlib's `Hyperreal`) with `ε`
  infinitesimal gives the book's absolute setting; instantiating `K := ℝ`
  with `ε` the Planck length (or the resolution of an instrument) gives the
  relative/physical setting.  Because the exact identities hold for *every*
  `ε > 0`, no transfer principle is needed to use them in either setting.
-/

namespace QE

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Centre of the point-sphere with lattice index `k`. -/
def centre (ε : K) (k : ℤ) : K := 2 * ε * k

/-- The lattice spacing, i.e. the diameter of a point-sphere. -/
def spacing (ε : K) : K := 2 * ε

/-- Granular (lossless) measure of a finite one-dimensional configuration:
each point contributes its diameter `2ε`. -/
def mu (ε : K) (A : Finset ℤ) : K := 2 * ε * A.card

/-- Granular measure in dimension `n`: each point contributes the volume
`(2ε)^n` of its Voronoi cell. -/
def muN (n : ℕ) (ε : K) (A : Finset (Fin n → ℤ)) : K := (2 * ε) ^ n * A.card

/-- Forward granular derivative. -/
def Dp (ε : K) (f : K → K) (x : K) : K := (f (x + 2 * ε) - f x) / (2 * ε)

/-- Backward granular derivative. -/
def Dm (ε : K) (f : K → K) (x : K) : K := (f x - f (x - 2 * ε)) / (2 * ε)

/-- Central granular derivative: the difference of `f` across the two poles
of the point-sphere centred at `x`. -/
def Dc (ε : K) (f : K → K) (x : K) : K := (f (x + ε) - f (x - ε)) / (2 * ε)

/-- Granular integral over the half-open run of `n` cells starting at the
centre `a`: `∑_{k<n} f(a + 2εk) · 2ε`. -/
def gint (ε : K) (f : K → K) (a : K) (n : ℕ) : K :=
  ∑ k ∈ Finset.range n, f (a + 2 * ε * k) * (2 * ε)

/-- Granular falling power `x (x - 2ε) ⋯ (x - 2(k-1)ε)`. -/
def fall (ε : K) (x : K) (k : ℕ) : K :=
  ∏ j ∈ Finset.range k, (x - 2 * ε * j)

end QE

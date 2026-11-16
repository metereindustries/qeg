-- SPDX-License-Identifier: MIT
-- Copyright 2026 Metere Industries, Inc. Author: Alfredo Metere.
-- Quasi-Euclidean Granular Geometry. Any derivative work must carry this notice:
--   This work is derivative of the Quasi-Euclidean Granular Geometry book
--   authored by Alfredo Metere. Copyright 2026 Metere Industries, Inc.
--   All rights reserved
-- See LICENSE.md and NOTICE.

import Lean

/-!
# Lebesgue-dependency checker

`lake env lean --run LebesgueCheck.lean <names-file>` reads one constant name per
line and, for each, explores the transitive closure of constants used in its
statement and proof (through all of Mathlib).  It reports `CLEAN` if no
Lebesgue-measure or integration constant is reachable, and otherwise `LEBESGUE`
followed by one dependency path from the constant to the offending marker.

The book's rule: granular (exact) results must be CLEAN; Lebesgue may appear
only in shadow/comparison results, where it is the lossy classical target.
-/

open Lean

/-- Constants whose use means "Lebesgue measure or Lebesgue/Bochner/interval
integration is used". -/
def markers : List Name :=
  [`MeasureTheory.MeasureSpace.volume, `Real.measureSpace,
   `MeasureTheory.integral, `MeasureTheory.lintegral, `intervalIntegral,
   `MeasureTheory.Measure.addHaar]

def markerSet : NameSet := markers.foldl (·.insert ·) {}

/-- Breadth-first search from `root`; returns a path to a marker if any. -/
def findPath (env : Environment) (root : Name) : Option (List Name) := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array Name := #[root]
  let mut i := 0
  while i < queue.size do
    let c := queue[i]!
    i := i + 1
    if markerSet.contains c then
      -- reconstruct path
      let mut path := [c]
      let mut cur := c
      while cur != root do
        cur := parent.getD cur root
        path := cur :: path
      return some path
    match env.find? c with
    | none => pure ()
    | some info =>
      let used := info.type.getUsedConstants ++
        (match info.value? (allowOpaque := true) with
         | some v => v.getUsedConstants
         | none => #[])
      for d in used do
        unless seen.contains d do
          seen := seen.insert d
          parent := parent.insert d c
          queue := queue.push d
  return none

def main (args : List String) : IO UInt32 := do
  let some file := args.head? | IO.eprintln "usage: LebesgueCheck <names-file>"; return 2
  let names := (← IO.FS.lines file).toList.filter (· ≠ "") |>.map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `QuasiEuclidean }] {} (trustLevel := 1024)
  for n in names do
    if !env.contains n then
      IO.println s!"UNKNOWN {n}"
    else
      match findPath env n with
      | none => IO.println s!"CLEAN {n}"
      | some p => IO.println s!"LEBESGUE {n} :: {" -> ".intercalate (p.map toString)}"
  return 0

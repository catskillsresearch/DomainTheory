/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example44
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise419.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise419

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (ii′) for `{0,1}*`.** The two successor ranges are disjoint:
`0σ ≠ 1τ`. -/
theorem peano_cons_disjoint (σ τ : Str) : (false :: σ) ≠ (true :: τ) := by
  simp

end DomainTheory.Neighborhood.Exercise419

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example44
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise419.Basic


namespace DomainTheory.Neighborhood.Exercise419

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (i) for `{0,1}*`.** `Λ` is not a successor: `[] ≠ b :: σ`. -/
theorem peano_nil_ne_cons (b : Bool) (σ : Str) : ([] : Str) ≠ b :: σ := by
  simp

end DomainTheory.Neighborhood.Exercise419

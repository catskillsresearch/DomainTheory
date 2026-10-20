/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
















/-- `σΣ* = Σ*` iff `σ = Λ`. -/
theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil

end DomainTheory.Neighborhood.Exercise516

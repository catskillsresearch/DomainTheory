/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise118.Basic


set_option linter.unusedSimpArgs false

namespace DomainTheory.Neighborhood



namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)










/-- **Exercise 1.18 — `leastFilter` is least.** Any filter `z` with `C ⊆ z` contains
`leastFilter C`. -/
theorem leastFilter_le (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) (z : V.Element) (hz : ∀ W ∈ C, z.mem W) :
    V.leastFilter C hCsub hC ≤ z := by
  rintro Y ⟨hYmem, n, X, hXC, hsub⟩
  exact z.up_mem (z.mem_interUpTo X (fun i hi => hz (X i) (hXC i hi))) hYmem hsub

end NeighborhoodSystem
end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem41.Basic
import DomainTheory.Neighborhood.Theorem41.mem_iterElem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
















/-- The approximants form an increasing chain: `n ≤ m ⟹ fⁿ(⊥) ⊑ fᵐ(⊥)`. -/
theorem iterElem_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) :
    f.iterElem n ≤ f.iterElem m := by
  intro X hX
  rw [mem_iterElem] at hX ⊢
  exact rel_master_mono f hnm hX

end ApproximableMap
end DomainTheory.Neighborhood

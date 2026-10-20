/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise321.Basic
import DomainTheory.Neighborhood.Exercise321.step_master_right


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








theorem step_eq_univ_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = Set.univ ↔ Z = V₁.master := by
  constructor
  · intro h
    -- the empty-list least map relates `Y` only to `Δ₂`; it lies in `[Y, Z] = univ`
    have hmem : leastMap (V₀ := V₀) (V₁ := V₁) ([] : List (Set α × Set β))
        (by simp) (fun {X} _ => by rw [interYs_nil]; exact V₁.master_mem) ∈ step Y Z := by
      rw [h]; exact Set.mem_univ _
    rw [mem_step, leastMap_rel] at hmem
    have : V₁.master ⊆ Z := by rw [← interYs_nil V₁.master Y]; exact hmem.2.2
    exact Set.Subset.antisymm (V₁.sub_master hZ) this
  · rintro rfl; exact step_master_right Y hY

end DomainTheory.Neighborhood

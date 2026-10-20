/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Exercise120
import Mathlib.Tactic
import DomainTheory.Neighborhood.Definition79.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)



/-- Membership in a finite union of down-sets: `z ∈ ⋃_{X∈L} ↓X ↔ ∃ X ∈ L, z ∈ ↓X`. -/
theorem mem_PDunion {L : List (Set α)} {z : Set α} :
    z ∈ (⋃ X ∈ L, V.upSet X) ↔ ∃ X ∈ L, z ∈ V.upSet X := by
  simp only [Set.mem_iUnion, exists_prop]

end NeighborhoodSystem
end DomainTheory.Neighborhood

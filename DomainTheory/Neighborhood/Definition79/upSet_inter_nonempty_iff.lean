/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import DomainTheory.Neighborhood.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Definition79.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)




/-- **Definition 7.9 (remark 1).** "`↓X ∩ ↓Y ≠ ∅` iff `{X, Y}` is consistent in `𝒟`." The
down-sets `↓X`, `↓Y` meet exactly when `X, Y` have a common lower neighbourhood `Z ⊆ X ∩ Y`. -/
theorem upSet_inter_nonempty_iff {X Y : Set α} :
    (V.upSet X ∩ V.upSet Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  rw [V.upSet_inter]
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood

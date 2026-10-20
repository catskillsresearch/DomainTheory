/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem85.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}



/-- **`fixedNbhd a ◁ E`, unconditionally.** The consistency clause is the same monotonicity +
intersectivity calculation as `fixedNbhd`'s own `inter_mem`, just without needing the extra
consistency witness `Z`. -/
theorem fixedNbhd_subsystem (a : ApproximableMap E E) : fixedNbhd a ◁ E where
  master_eq := rfl
  sub := fun h => h.1
  inter_closed := by
    rintro X Y ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ hEXY
    have h1 : a.rel (X ∩ Y) X := a.mono hXa Set.inter_subset_left subset_rfl hEXY hXE
    have h2 : a.rel (X ∩ Y) Y := a.mono hYa Set.inter_subset_right subset_rfl hEXY hYE
    exact ⟨hEXY, a.inter_right h1 h2⟩

end DomainTheory.Neighborhood

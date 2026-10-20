/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic
import DomainTheory.Neighborhood.Exercise827.hii_hard_direction


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap






















































/-- **Exercise 8.27(b)(3), in full: `piD d` satisfies Scott's step-closure formula (ii), for *any*
`d` at all** (`d`'s polymorphism is not needed). Combines the reduction (b)(3)(a) with the easy
(`hii_easy_direction`) and now-closed hard (`hii_hard_direction`) halves. -/
theorem hii_piD (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  rw [piD_toElementMap_mem_iff]
  constructor
  · rintro ⟨hYE, hmem⟩
    exact ⟨hYE, hii_hard_direction d x hYE hmem⟩
  · rintro ⟨hYE, X, hXx, hXY, hXX⟩
    have := hii_easy_direction d x hYE hXx hXY hXX
    rwa [piD_toElementMap_mem_iff] at this

end DomainTheory.Neighborhood

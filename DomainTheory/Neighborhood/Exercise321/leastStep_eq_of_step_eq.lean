/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise321.Basic
import DomainTheory.Neighborhood.Exercise321.leastStep_mem
import DomainTheory.Neighborhood.Exercise321.leastStep_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}









/-- The least elements of equal step neighbourhoods coincide. -/
theorem leastStep_eq_of_step_eq {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z')
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') :
    leastStep Y Z hY hZ = leastStep Y' Z' hY' hZ' := by
  apply le_antisymm
  · exact leastStep_le hY hZ (h ▸ leastStep_mem hY' hZ')
  · exact leastStep_le hY' hZ' (h.symm ▸ leastStep_mem hY hZ)

end DomainTheory.Neighborhood

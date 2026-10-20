/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise407
import DomainTheory.Neighborhood.Exercise410
import DomainTheory.Neighborhood.Exercise411.Basic
import DomainTheory.Neighborhood.Exercise411.inclMap_toElementMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- The inclusion is strict: `ι(⊥) = ⊥`. -/
theorem inclMap_bot (a : V.Element) : (inclMap a).toElementMap (relSystem a).bot = V.bot := by
  rw [inclMap_toElementMap]
  apply Element.ext
  intro Y
  rw [mem_bot]
  constructor
  · rintro ⟨hVY, W, _, hbW, hWY⟩
    rw [mem_bot] at hbW
    rw [hbW] at hWY
    exact Set.Subset.antisymm (V.sub_master hVY) hWY
  · rintro rfl
    exact ⟨V.master_mem, V.master, a.master_mem, (relSystem a).bot.master_mem, subset_rfl⟩

end ApproximableMap
end DomainTheory.Neighborhood

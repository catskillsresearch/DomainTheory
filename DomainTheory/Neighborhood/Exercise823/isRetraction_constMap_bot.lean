/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise816
import DomainTheory.Neighborhood.Exercise823.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


theorem isRetraction_constMap_bot (E : NeighborhoodSystem α) :
    IsRetraction (constMap E E.bot) := by
  show (constMap E E.bot).comp (constMap E E.bot) = constMap E E.bot
  apply ApproximableMap.ext
  intro X Z
  simp only [comp_rel, constMap_rel, mem_bot]
  constructor
  · rintro ⟨Y, ⟨hX, rfl⟩, -, hZ⟩
    exact ⟨hX, hZ⟩
  · rintro ⟨hX, hZ⟩
    exact ⟨E.master, ⟨hX, rfl⟩, E.master_mem, hZ⟩

end Exercise823
end DomainTheory.Neighborhood

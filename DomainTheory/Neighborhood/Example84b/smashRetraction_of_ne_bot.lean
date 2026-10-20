/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example84
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Example84b.Basic
import DomainTheory.Neighborhood.Example84b.smashRetraction_mem_iff


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






theorem smashRetraction_of_ne_bot {z : (prod D E).Element} (hx : z.fst ≠ D.bot)
    (hy : z.snd ≠ E.bot) : smashRetraction.toElementMap z = z := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨-, -, hzZ⟩⟩
    · rw [hZeq]; exact z.master_mem
    · exact hzZ
  · intro hzZ
    exact ⟨z.sub hzZ, Or.inr ⟨hx, hy, hzZ⟩⟩

end Smash
end DomainTheory.Neighborhood

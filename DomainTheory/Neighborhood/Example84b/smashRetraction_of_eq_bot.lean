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






theorem smashRetraction_of_eq_bot {z : (prod D E).Element} (hz : z.fst = D.bot ∨ z.snd = E.bot) :
    smashRetraction.toElementMap z = (prod D E).bot := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hx, hy, -⟩⟩
    · rfl
    · exact absurd hz (by simp [hx, hy])
  · rintro rfl
    exact ⟨(prod D E).master_mem, Or.inl rfl⟩

end Smash
end DomainTheory.Neighborhood

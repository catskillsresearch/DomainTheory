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
import DomainTheory.Neighborhood.Example84b.smashRetraction_of_ne_bot
import DomainTheory.Neighborhood.Example84b.smashRetraction_of_eq_bot


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






theorem isRetraction_smashRetraction : IsRetraction (smashRetraction (D := D) (E := E)) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_comp]
  by_cases hx : z.fst = D.bot
  · rw [smashRetraction_of_eq_bot (Or.inl hx),
      smashRetraction_of_eq_bot (Or.inl prod_bot_fst)]
  · by_cases hy : z.snd = E.bot
    · rw [smashRetraction_of_eq_bot (Or.inr hy),
        smashRetraction_of_eq_bot (Or.inr prod_bot_snd)]
    · rw [smashRetraction_of_ne_bot hx hy, smashRetraction_of_ne_bot hx hy]

end Smash
end DomainTheory.Neighborhood

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
import DomainTheory.Neighborhood.Example84b.toApproxMap_injective


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







section Strict








theorem isRetraction_strictRetraction : IsRetraction (strictRetraction (D := D) (E := E)) := by
  apply ext_of_toElementMap
  intro φ
  rw [toElementMap_comp]
  apply toApproxMap_injective
  apply ext_of_toElementMap
  intro y
  by_cases hy : y = D.bot
  · rw [hy, strictRetraction_apply_bot, strictRetraction_apply_bot]
  · rw [strictRetraction_apply_of_ne_bot hy, strictRetraction_apply_of_ne_bot hy]

end Strict
end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Exercise326Sum
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise819.Basic
import DomainTheory.Neighborhood.Exercise819.TD_trichotomy
import DomainTheory.Neighborhood.Exercise819.toApproxMap_pairToFun
import DomainTheory.Neighborhood.Exercise819.toElementMap_funToPair


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **`pairToFun ∘ funToPair ≤ I`.** For every `φ : T → E`, feeding `(φ(true), φ(false))` back
through `cond` gives a map agreeing with `φ` at `true`/`false` and `≤ φ` at `⊥` (`E.bot ≤`
anything). Case split on `T`'s three elements (`TD_trichotomy`). -/
theorem pairToFun_comp_funToPair_le :
    (pairToFun (E := E)).comp funToPair ≤ idMap (funSpace TD E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair]
  apply (funSpaceEquiv TD E).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro t
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [toApproxMap_pairToFun, Exercise326.cond_bot]; exact E.bot_le _
  · rw [toApproxMap_pairToFun, Exercise326.cond_true]
  · rw [toApproxMap_pairToFun, Exercise326.cond_false]

end Prod
end DomainTheory.Neighborhood

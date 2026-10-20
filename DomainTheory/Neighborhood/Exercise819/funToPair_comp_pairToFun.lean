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
import DomainTheory.Neighborhood.Exercise819.toApproxMap_pairToFun
import DomainTheory.Neighborhood.Exercise819.toElementMap_funToPair


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **`funToPair ∘ pairToFun = I`.** `(x, y) ↦ (λt. cond(t,x,y)) ↦ (cond(true,x,y),
cond(false,x,y)) = (x, y)`. -/
theorem funToPair_comp_pairToFun : (funToPair (E := E)).comp pairToFun = idMap (prod E E) := by
  apply ext_of_toElementMap
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair, toApproxMap_pairToFun,
    toApproxMap_pairToFun, Exercise326.cond_true, Exercise326.cond_false]

end Prod
end DomainTheory.Neighborhood

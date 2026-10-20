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
import DomainTheory.Neighborhood.Exercise819.toElementMap_swapProdT


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}



theorem toApproxMap_pairToFun (x y : E.Element) (t : TD.Element) :
    (toApproxMap ((pairToFun (E := E)).toElementMap (pair x y))).toElementMap t
      = (cond E).toElementMap (pair t (pair x y)) := by
  rw [pairToFun, toElementMap_curry_apply, toElementMap_comp, toElementMap_swapProdT]

end Prod
end DomainTheory.Neighborhood

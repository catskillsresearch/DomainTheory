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


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


theorem toElementMap_swapProdT (x y : E.Element) (t : TD.Element) :
    (swapProdT (E := E)).toElementMap (pair (pair x y) t) = pair t (pair x y) := by
  simp only [swapProdT, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁, fst_pair,
    snd_pair]

end Prod
end DomainTheory.Neighborhood

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
import DomainTheory.Neighborhood.Exercise819.toElementMap_sumToProdT


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`condSum ∘ sumToProdT = I`.** Scott's identity `cond_which`, transported through
`condSumEmb`. -/
theorem condSum_comp_sumToProdT :
    (condSum E E hE hE).comp (sumToProdT hE) = idMap (sum E E hE hE) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_sumToProdT, condSum, toElementMap_comp,
    condSumEmb_toElementMap]
  exact cond_which w

end Sum
end DomainTheory.Neighborhood

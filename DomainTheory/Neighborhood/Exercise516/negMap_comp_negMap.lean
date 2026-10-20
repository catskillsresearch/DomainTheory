/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise419
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise516.Basic
import DomainTheory.Neighborhood.Exercise516.map_ext_C


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}














/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg ∘ neg = id` as approximable maps: it suffices to
check on the finite elements `σ⊥`, `σ`, where it is `flip ∘ flip = id`. -/
theorem negMap_comp_negMap : negMap.comp negMap = idMap C := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, negMap_strBot, negMap_strBot, flip_flip, toElementMap_idMap]
  · intro σ
    rw [toElementMap_comp, negMap_strElem, negMap_strElem, flip_flip, toElementMap_idMap]

end DomainTheory.Neighborhood.Exercise516

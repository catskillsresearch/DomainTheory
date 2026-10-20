/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise419
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise516.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}








/-- `tail(b(σ)) = σ`. -/
theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl

end DomainTheory.Neighborhood.Exercise516

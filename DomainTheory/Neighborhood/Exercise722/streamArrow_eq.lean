/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Set.Insert
import DomainTheory.Neighborhood.Exercise722.Basic
import DomainTheory.Neighborhood.Exercise722.prependMap_toElementMap


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`σ⃗ = σ·σ⃗`** (Scott's defining equation), unconditionally. -/
theorem streamArrow_eq (σ : List Bool) :
    mulElem (emb σ) (streamArrow σ) = streamArrow σ := by
  rw [← prependMap_toElementMap]
  exact toElementMap_fixElement (prependMap σ)

end Exercise722
end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem41.Basic
import DomainTheory.Neighborhood.Theorem41.fixElement_le_of_toElementMap_le
import DomainTheory.Neighborhood.Theorem41.fixMap_toElementMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2(ii) (Scott 1981, PRG-19).** `f(x) ⊆ x ⟹ fix(f) ⊆ x`: `fix` lands in the least
pre-fixed point. -/
theorem fixMap_least (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) {z : V.Element}
    (hz : (toApproxMap φ).toElementMap z ≤ z) : (fixMap V).toElementMap φ ≤ z := by
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap φ) hz

end DomainTheory.Neighborhood

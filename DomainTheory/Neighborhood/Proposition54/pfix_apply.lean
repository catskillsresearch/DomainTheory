/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Proposition54.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap



/-- `pfix τ (x) = !y. τ(x, y)`, the least fixed point of the section at `x`. -/
theorem pfix_apply (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    (pfix τ).toElementMap x = (section₂ τ x).fixElement := by
  rw [pfix, toElementMap_comp, fixMap_toElementMap, section₂]

end ApproximableMap
end DomainTheory.Neighborhood

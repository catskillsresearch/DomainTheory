/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Proposition54.Basic
import DomainTheory.Neighborhood.Proposition54.sectionu2082_apply
import DomainTheory.Neighborhood.Proposition54.pfix_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- `pfix τ` is a fixed point of `recOp τ` (pointwise: `τ(x, pfix τ x) = pfix τ x`). -/
theorem pfix_isFixed (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    τ.toElementMap (pair x ((pfix τ).toElementMap x)) = (pfix τ).toElementMap x := by
  rw [pfix_apply, ← section₂_apply, toElementMap_fixElement]

end ApproximableMap
end DomainTheory.Neighborhood

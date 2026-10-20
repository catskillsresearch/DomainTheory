/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Proposition53.Basic
import DomainTheory.Neighborhood.Proposition53.sectionX_apply
import DomainTheory.Neighborhood.Proposition53.secFixX_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap



/-- `!x. τ(x, y)` is a fixed point of the section: `τ(!x.τ(x,y), y) = !x.τ(x,y)`. -/
theorem secFixX_isFixed (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    τ.toElementMap (pair ((secFixX τ).toElementMap y) y) = (secFixX τ).toElementMap y := by
  rw [secFixX_apply, ← sectionX_apply, toElementMap_fixElement]

end ApproximableMap
end DomainTheory.Neighborhood

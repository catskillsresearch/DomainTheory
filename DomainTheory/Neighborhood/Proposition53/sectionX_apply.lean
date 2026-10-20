/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Proposition53.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


theorem sectionX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) (x : V₀.Element) :
    (sectionX τ y).toElementMap x = τ.toElementMap (pair x y) := by
  rw [sectionX, toElementMap_curry_apply, toElementMap_comp, swapC_apply]

end ApproximableMap
end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise319Sum
import DomainTheory.Neighborhood.Exercise326Sum.Basic
import DomainTheory.Neighborhood.Exercise326Sum.condSumEmb_toElementMap


namespace DomainTheory.Neighborhood.Exercise326

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}




/-- **Exercise 3.26.** `condSum(true, x, y) = in₀(x)`. -/
theorem condSum_true (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.trueElt (pair x y))
      = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_true]

end DomainTheory.Neighborhood.Exercise326

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise322.Basic
import DomainTheory.Neighborhood.Exercise322.toElementMap_compMap_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}



/-- **Exercise 3.22 (Scott 1981, PRG-19).** The relational form `comp(g, f) = g ∘ f`: the value of
`comp` at `⟨g, f⟩`, read back as an approximable map, is the composition of the approximable maps. -/
theorem toApproxMap_compMap (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
      = (toApproxMap Gφ).comp (toApproxMap Fφ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_compMap_apply, toElementMap_comp]

end DomainTheory.Neighborhood

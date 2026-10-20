/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Table55.Basic
import DomainTheory.Neighborhood.Table55.compC_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
























/-- `comp(g, f) = g ∘ f` (Scott's infix `g ∘ f`). -/
theorem compC_eq_comp (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ)) = (toApproxMap φ).comp (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, compC_apply]

end DomainTheory.Neighborhood

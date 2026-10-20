/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Table55.Basic
import DomainTheory.Neighborhood.Table55.funpairC_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}



























/-- `funpair(f)(g)` is the paired map `⟨f, g⟩` of Definition 3.3. -/
theorem funpairC_eq_paired (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element) :
    toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)
      = paired (toApproxMap φ) (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [funpairC_apply, toElementMap_paired]

end DomainTheory.Neighborhood

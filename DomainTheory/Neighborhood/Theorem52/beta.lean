/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Theorem52.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — β as a map equation.** Substituting the constant `σ` for
the bound variable: `(λx.τ)(σ) = τ[σ/x]`, where the left side first abstracts (`curry g`) then
applies to the constant `σ`, and the right side substitutes `σ` directly. Both are approximable
maps `Γ → 𝒟'` and they are equal. -/
theorem beta (g : ApproximableMap (prod V₀ V₁) V₂) (σ : V₁.Element) :
    (evalMap V₁ V₂).comp (paired (curry g) (constMap V₀ σ))
      = g.comp (paired (idMap V₀) (constMap V₀ σ)) := by
  apply ext_of_toElementMap
  intro v
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply, toElementMap_curry_apply,
    toElementMap_constMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

end Theorem52
end DomainTheory.Neighborhood

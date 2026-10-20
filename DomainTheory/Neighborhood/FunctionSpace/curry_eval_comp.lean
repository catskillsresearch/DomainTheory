/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic
import DomainTheory.Neighborhood.FunctionSpace.uncurry_eq


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

















































variable {V₂ : NeighborhoodSystem γ}
















/-- **Theorem 3.12(iii) (Scott 1981, PRG-19).** `curry (eval ∘ ⟨h ∘ p₀, p₁⟩) = h`. -/
theorem curry_eval_comp (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h := by
  rw [← uncurry_eq, curry_uncurry]

end DomainTheory.Neighborhood

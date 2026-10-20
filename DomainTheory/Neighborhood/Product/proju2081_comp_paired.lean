/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product.Basic
import DomainTheory.Neighborhood.Product.toElementMap_paired


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}










variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





















variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap










/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₁ ∘ ⟨f, g⟩ = g`. -/
theorem proj₁_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₁ V₀ V₁).comp (paired f g) = g := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₁, snd_pair]

end DomainTheory.Neighborhood

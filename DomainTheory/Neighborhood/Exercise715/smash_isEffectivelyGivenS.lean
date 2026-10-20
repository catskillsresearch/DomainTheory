/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Exercise715.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}







variable (P₀ P₁)




/-- **Exercise 7.15 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem smash_isEffectivelyGivenS (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (smash V₀ V₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := h₀; obtain ⟨Q₁⟩ := h₁
  exact ⟨smashPresentation Q₀ Q₁⟩

end Smash
end DomainTheory.Neighborhood

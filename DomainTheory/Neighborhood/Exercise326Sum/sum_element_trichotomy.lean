/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise319Sum
public import DomainTheory.Neighborhood.Exercise326Sum.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise326

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
















/-- Trichotomy for a sum-element: it reaches the left copy, or the right copy, or is `⊥`. -/
theorem sum_element_trichotomy (x : (sum V₀ V₁ h₀ h₁).Element) :
    (∃ X, V₀.mem X ∧ x.mem (inj₀ X)) ∨ (∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) ∨
      (∀ W, x.mem W → W = (sum V₀ V₁ h₀ h₁).master) := by
  by_cases hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)
  · exact Or.inl hL
  by_cases hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)
  · exact Or.inr (Or.inl hR)
  refine Or.inr (Or.inr ?_)
  intro W hxW
  rcases x.sub hxW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rfl
  · exact absurd ⟨X, hX, hxW⟩ hL
  · exact absurd ⟨Y, hY, hxW⟩ hR

end DomainTheory.Neighborhood.Exercise326

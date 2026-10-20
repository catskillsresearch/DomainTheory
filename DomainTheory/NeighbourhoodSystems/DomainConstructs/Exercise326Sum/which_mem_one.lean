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
















/-- `which(x)` selects `false` (`{1} ∈ which x`) exactly when `x` reaches into the right copy. -/
theorem which_mem_one {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.one
      ↔ ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨_, hc⟩ | ⟨⟨Y, hY, rfl⟩, _⟩ | ⟨_, hc⟩
    · rcases hc with h | h
      · exact absurd h one_ne_master
      · exact absurd h zero_ne_one.symm
    · exact ⟨Y, hY, hWx⟩
    · exact absurd hc one_ne_master
  · rintro ⟨Y, hY, hWx⟩
    exact ⟨inj₁ Y, hWx, Or.inr (Or.inr ⟨Y, hY, rfl⟩), Example12.mem_one,
      Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, Or.inr rfl⟩)⟩

end DomainTheory.Neighborhood.Exercise326

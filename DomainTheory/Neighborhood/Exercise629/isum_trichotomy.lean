/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import DomainTheory.Neighborhood.Exercise629.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}







variable {D : ∀ i, NeighborhoodSystem (α i)}
















/-- **Exercise 6.29 — sum trichotomy.** Every element of `∑_i D_i` either reaches into some summand
or is the basepoint `⊥`. (Prop-level and genuinely classical: the case split is excluded middle on
whether `z` reaches a summand, so this depends on `Classical.choice`.) -/
theorem isum_trichotomy {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) :
    (∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)) ∨
      (∀ W, z.mem W → W = (isum D hne).master) := by
  by_cases h : ∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)
  · exact Or.inl h
  · refine Or.inr fun W hW => ?_
    rcases z.sub hW with rfl | ⟨i, X, hX, rfl⟩
    · rfl
    · exact absurd ⟨i, X, hX, hW⟩ h

end Exercise629
end DomainTheory.Neighborhood

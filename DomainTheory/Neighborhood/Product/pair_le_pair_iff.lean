/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}










variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}














/-- **Proposition 3.2(i) (Scott 1981, PRG-19).** `⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pair_le_pair_iff {x x' : V₀.Element} {y y' : V₁.Element} :
    pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd X V₁.master) ⟨X, V₁.master, hX, y.master_mem, rfl⟩
      obtain ⟨rfl, _⟩ := prodNbhd_injective heq
      exact hX'
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd V₀.master Y) ⟨V₀.master, Y, x.master_mem, hY, rfl⟩
      obtain ⟨_, rfl⟩ := prodNbhd_injective heq
      exact hY'
  · rintro ⟨hx, hy⟩ W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, hx X hX, hy Y hY, rfl⟩

end DomainTheory.Neighborhood

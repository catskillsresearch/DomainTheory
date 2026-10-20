/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

/-- The three index shapes: `0` (master `Γ`), `2a+1` (leaf), `2a+2` (node). Choice-free. -/
theorem nat_shape (n : ℕ) : n = 0 ∨ (∃ a, n = 2 * a + 1) ∨ (∃ a, n = 2 * a + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  · rcases Nat.lt_or_ge (n % 2) 1 with h | h
    · exact Or.inr (Or.inr ⟨n / 2 - 1, by omega⟩)
    · exact Or.inr (Or.inl ⟨n / 2, by omega⟩)

end Proposition77

end DomainTheory.NeighbourhoodSystems

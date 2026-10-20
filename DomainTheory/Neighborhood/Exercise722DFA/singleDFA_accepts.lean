/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Regular
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option
import DomainTheory.Neighborhood.Exercise722DFA.Basic
import DomainTheory.Neighborhood.Exercise722DFA.singleDFA_evalFrom


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability







/-- **The single-word DFA recognises exactly `{σ}`.** -/
theorem singleDFA_accepts (σ : List Bool) : (singleDFA σ).accepts = {σ} := by
  ext w
  show (singleDFA σ).evalFrom (some ⟨0, by omega⟩) w ∈ (singleDFA σ).accept ↔ _
  rw [singleDFA_evalFrom]
  by_cases h : w <+: List.drop (0 : ℕ) (σ : List Bool)
  · rw [dite_eq_left h, List.drop_zero] at *
    show some (⟨0 + w.length, _⟩ : Fin (σ.length + 1)) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff, Option.some.injEq, Fin.mk.injEq, Nat.zero_add]
    constructor
    · intro hlen; exact h.eq_of_length hlen
    · intro hw; subst hw; rfl
  · rw [dite_eq_right h, List.drop_zero] at *
    show (none : SingleState σ) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hcontra; exact absurd hcontra (by simp)
    · intro hw; subst hw; exact absurd List.prefix_rfl h

end Exercise722
end DomainTheory.Neighborhood

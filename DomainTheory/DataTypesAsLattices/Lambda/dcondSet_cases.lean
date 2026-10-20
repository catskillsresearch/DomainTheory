/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_cases (z : Pomega) :
    (0 ∈ z ∧ ¬ ∃ k, k + 1 ∈ z) ∨
      (0 ∉ z ∧ ∃ k, k + 1 ∈ z) ∨
        (0 ∈ z ∧ ∃ k, k + 1 ∈ z) ∨
          (0 ∉ z ∧ ¬ ∃ k, k + 1 ∈ z) := by
  by_cases h0 : 0 ∈ z
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inr (Or.inl ⟨h0, hp⟩))
    · exact Or.inl ⟨h0, hp⟩
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inl ⟨h0, hp⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h0, hp⟩))

end DomainTheory.DataTypesAsLattices

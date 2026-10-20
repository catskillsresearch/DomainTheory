/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices




























/-- **Scott 1976, (2.10).** Abstraction distributes over union. -/
theorem eq_2_10 (τ σ : Pomega → Pomega) :
    graph τ ∪ graph σ = graph (fun x => τ x ∪ σ x) := by
  ext p
  constructor
  · intro hp
    rcases hp with h | h
    · rcases h with ⟨n, m, hp, hm⟩
      exact ⟨n, m, hp, Or.inl hm⟩
    · rcases h with ⟨n, m, hp, hm⟩
      exact ⟨n, m, hp, Or.inr hm⟩
  · intro h
    rcases h with ⟨n, m, hp, hm⟩
    rcases hm with hm | hm
    · exact Or.inl ⟨n, m, hp, hm⟩
    · exact Or.inr ⟨n, m, hp, hm⟩

end DomainTheory.DataTypesAsLattices

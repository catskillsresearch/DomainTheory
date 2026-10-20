/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices




























/-- **Scott 1976, (2.12).** Abstraction distributes over intersection. -/
theorem eq_2_12 (τ σ : Pomega → Pomega) :
    graph τ ∩ graph σ = graph (fun x => τ x ∩ σ x) := by
  ext p
  constructor
  · intro ⟨hτ, hσ⟩
    rcases hτ with ⟨n, m, hpτ, hmτ⟩
    rcases hσ with ⟨n', m', hpσ, hmσ⟩
    have hp' : pair n m = pair n' m' := hpτ.symm.trans hpσ
    obtain ⟨rfl, rfl⟩ := pair_inj hp'
    exact ⟨n, m, hpτ, hmτ, hmσ⟩
  · intro h
    rcases h with ⟨n, m, hp, hmτ, hmσ⟩
    exact ⟨⟨n, m, hp, hmτ⟩, ⟨n, m, hp, hmσ⟩⟩

end DomainTheory.DataTypesAsLattices

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.accepts_card_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.accepts_shorten_step

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

theorem exists_accepted_word_short (h : M.accepts.Nonempty) :
    ∃ w, w.length < Fintype.card σ ∧ w ∈ M.accepts := by
  by_cases hσ : Fintype.card σ = 0
  · obtain ⟨x, hx⟩ := h
    exact (accepts_card_zero hσ hx).elim
  · obtain ⟨x, hx⟩ := h
    exact Nat.strongRecOn x.length
      (motive := fun n =>
        ∀ w, w.length = n → w ∈ M.accepts → ∃ u, u.length < Fintype.card σ ∧ u ∈ M.accepts)
      (fun n ih w hwlen hw => by
        by_cases hlt : n < Fintype.card σ
        · exact ⟨w, hwlen ▸ hlt, hw⟩
        · have hge : Fintype.card σ ≤ n := Nat.not_lt.mp hlt
          obtain ⟨y, hy, hylt⟩ := accepts_shorten_step hw (hwlen.symm ▸ hge)
          exact ih y.length (Nat.lt_of_lt_of_eq hylt hwlen) y rfl hy)
      x rfl hx

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.appendCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.stepFun_funListOf_appendCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.selectFn_isOne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_pos
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_neg
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_inter_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.consPairChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem consPairChar_spec (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (n m : ℕ) :
    consPairChar gN n m = 1 ↔
      ∃ k, Xenum P₀ P₁ gN k ⊆ Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m := by
  have hcons_iff : (∃ k, Xenum P₀ P₁ gN k ⊆ Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m) ↔
      (Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m).Nonempty := by
    constructor
    · rintro ⟨k, hk⟩; exact (Xenum_nonempty P₀ P₁ gN hgN k).mono hk
    · intro hne
      exact ⟨interIdx gN n m, (Xenum_inter_eq P₀ P₁ gN hgN n m hne).subset⟩
  rw [hcons_iff]
  unfold consPairChar
  by_cases hn : gN n = 1
  · rw [selectFn_isOne, ite_eq_left hn, selectFn_isOne]
    by_cases hm : gN m = 1
    · rw [ite_eq_left hm, hgN (appendCode n m), Xenum_pos P₀ P₁ hn, Xenum_pos P₀ P₁ hm,
        ← stepFun_funListOf_appendCode P₀ P₁ n m]
    · rw [ite_eq_right hm, Xenum_pos P₀ P₁ hn, Xenum_neg P₀ P₁ hm, Set.inter_univ]
      exact iff_of_true rfl ((hgN n).mp hn)
  · rw [selectFn_isOne, ite_eq_right hn, Xenum_neg P₀ P₁ hn, Set.univ_inter]
    exact iff_of_true rfl (Xenum_nonempty P₀ P₁ gN hgN m)

end DomainTheory.NeighbourhoodSystems

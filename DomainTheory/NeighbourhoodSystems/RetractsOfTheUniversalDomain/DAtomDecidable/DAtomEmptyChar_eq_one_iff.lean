/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFoldCode_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)









variable (incl : ℕ → ℕ)


theorem DAtomEmptyChar_eq_one_iff
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    (hincl : ∀ n m, incl (Nat.pair n m) = 1 ↔ P.X n ⊆ P.X m) (posC negC : ℕ) :
    DAtomEmptyChar P cons incl posC negC = 1 ↔
      DAtom P (decodeList posC) (decodeList negC) = ∅ := by
  rw [DAtom_eq_empty_iff P cons hcons, ← meetFoldCode_eq]
  set r := meetFoldCode P cons posC with hrdef
  unfold DAtomEmptyChar
  by_cases hok : r.unpair.1 = 1
  · rw [(isOne_eq_one_iff _).mpr hok, selectFn_one, existsListChar_eq_one_iff]
    simp only [ne_eq, hok, not_true_eq_false, false_or]
    constructor
    · rintro ⟨j, hj, hgj⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hgj
      exact ⟨j, hj, (hincl _ _).mp hgj⟩
    · rintro ⟨j, hj, hsub⟩
      refine ⟨j, hj, ?_⟩
      simp only [unpair_pair_fst, unpair_pair_snd]
      exact (hincl _ _).mpr hsub
  · rw [isOne_of_ne_one hok, selectFn_zero]
    simp only [ne_eq, hok, not_false_eq_true, true_or]

end DomainTheory.NeighbourhoodSystems

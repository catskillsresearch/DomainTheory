/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.deltaOf_mod_two_pow_of_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.mem_UX_YseqCode_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

























































theorem atomUCode_succ_true {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = true) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) ∩ UX (YseqCode P n) := by
  set j := k % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  have hagree : ∀ i < n + 1, deltaOf k i = deltaOf (j + 2 ^ n) i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hi', hjdef, deltaOf_mod_two_pow_of_lt hi']
    · rw [deltaOf_two_pow_add_self hjlt, hδ]
  obtain ⟨hpos_eq, hneg_eq, hcode_eq⟩ := atomUCodeState_congr P hagree
  have hempty_eq : atomUEmpty P (n + 1) (j + 2 ^ n) = 0 := by
    have heq : atomUEmpty P (n + 1) (j + 2 ^ n) = atomUEmpty P (n + 1) k := by
      unfold atomUEmpty; rw [hpos_eq, hneg_eq]
    rw [heq]; exact hne
  apply Set.Subset.antisymm
  · have hsub1 : UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := atomUCode_subset P hne
    have hsub2 : UX (atomUCode P (n + 1) k) ⊆ UX (YseqCode P n) := by
      rw [hcode_eq]
      intro z hz
      exact (mem_UX_YseqCode_iff P n z).mpr ⟨j, hjlt, hempty_eq, hz⟩
    exact Set.subset_inter hsub1 hsub2
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
    by_cases hagree' : ∀ p < n, deltaOf (i + 2 ^ n) p = deltaOf k p
    · have hagreeFull : ∀ l < n + 1, deltaOf (i + 2 ^ n) l = deltaOf k l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
        · exact hagree' l hl'
        · rw [deltaOf_two_pow_add_self hilt, hδ]
      have hcode_eq'' : atomUCode P (n + 1) (i + 2 ^ n) = atomUCode P (n + 1) k :=
        (atomUCodeState_congr P hagreeFull).2.2
      rw [← hcode_eq'']; exact hz
    · push Not at hagree'
      obtain ⟨l, hl, hlne⟩ := hagree'
      have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) = ∅ :=
        atomUCode_disjoint P n (i + 2 ^ n) k (atomUEmpty_zero_of_succ P hie)
          (atomUEmpty_zero_of_succ P hne) ⟨l, hl, hlne⟩
      have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode_subset P hie hz
      have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) := ⟨hzB', hzB⟩
      rw [hd] at hzmem
      exact absurd hzmem (Set.mem_empty_iff_false z).mp

end DomainTheory.NeighbourhoodSystems

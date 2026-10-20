/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_nonempty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_inter_same_level
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_union_same_level

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem
















/-- **Scott's remark after Definition 8.7, transplanted to `V`**: every `V`-neighbourhood splits
into two disjoint proper `V`-neighbourhoods. Refine to one level finer via `upsample`, which
duplicates every set bit `ℓ` of `m` into a matching pair `(ℓ, ℓ + 2^k)`; peeling off *one*
representative bit `ℓ₀` (witnessing `X`'s non-emptiness) leaves its twin `ℓ₀ + 2^k` behind, so the
"rest" is guaranteed non-empty regardless of how many other bits `m` had. -/
theorem V_no_minimal {X : Set ℕ} (hX : V.mem X) :
    ∃ Y Z : Set ℕ, V.mem Y ∧ V.mem Z ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ Y ≠ X ∧ Z ≠ X := by
  obtain ⟨k, m, rfl, hne⟩ := hX
  obtain ⟨ℓ₀, hℓ₀, hbit⟩ := levelSet_nonempty_iff.mp hne
  have hstep : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  have hℓ₀2 : ℓ₀ < 2 ^ (k + 1) := by omega
  have hℓ₀' : ℓ₀ + 2 ^ k < 2 ^ (k + 1) := by omega
  set M := upsample k (k + 1) m with hM
  have hXM : levelSet k m = levelSet (k + 1) M := (levelSet_upsample (Nat.le_succ k)).symm
  have hMℓ₀ : M.testBit ℓ₀ = true := by
    rw [hM, testBit_upsample hℓ₀2, Nat.mod_eq_of_lt hℓ₀]; exact hbit
  have hMℓ₀' : M.testBit (ℓ₀ + 2 ^ k) = true := by
    rw [hM, testBit_upsample hℓ₀', Nat.add_mod_right, Nat.mod_eq_of_lt hℓ₀]; exact hbit
  set Y := levelSet (k + 1) (2 ^ ℓ₀) with hYdef
  set Z := levelSet (k + 1) (M ^^^ 2 ^ ℓ₀) with hZdef
  have hYmem : V.mem Y := ⟨k + 1, 2 ^ ℓ₀, rfl, levelSet_nonempty_iff.mpr ⟨ℓ₀, hℓ₀2, by simp⟩⟩
  have hZmem : V.mem Z := ⟨k + 1, M ^^^ 2 ^ ℓ₀, rfl,
    levelSet_nonempty_iff.mpr ⟨ℓ₀ + 2 ^ k, hℓ₀', by
      rw [Nat.testBit_xor, hMℓ₀']; simp⟩⟩
  have hInter : Y ∩ Z = ∅ := by
    rw [hYdef, hZdef, levelSet_inter_same_level]
    ext n
    simp only [mem_levelSet, Set.mem_empty_iff_false, iff_false, Nat.testBit_and, Bool.and_eq_true]
    rintro ⟨h1, h2⟩
    have hpos : n % 2 ^ (k + 1) = ℓ₀ := by
      by_contra hne'
      rw [Nat.testBit_two_pow] at h1
      exact hne' (of_decide_eq_true h1).symm
    rw [hpos, Nat.testBit_xor, hMℓ₀] at h2
    simp at h2
  have hUnion : Y ∪ Z = levelSet k m := by
    rw [hYdef, hZdef, levelSet_union_same_level, hXM]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_xor]
    rcases eq_or_ne i ℓ₀ with rfl | hi
    · simp [hMℓ₀]
    · simp [Ne.symm hi]
  have hYne : Y.Nonempty := (levelSet_nonempty_iff (k := k + 1) (m := 2 ^ ℓ₀)).mpr ⟨ℓ₀, hℓ₀2, by simp⟩
  have hZne : Z.Nonempty := (levelSet_nonempty_iff (k := k + 1) (m := M ^^^ 2 ^ ℓ₀)).mpr
    ⟨ℓ₀ + 2 ^ k, hℓ₀', by
      rw [Nat.testBit_xor, hMℓ₀']; simp⟩
  refine ⟨Y, Z, hYmem, hZmem, hInter, hUnion, ?_, ?_⟩
  · intro hEq
    apply hZne.ne_empty
    have hZsub : Z ⊆ Y := by rw [hEq]; exact hUnion ▸ Set.subset_union_right
    rw [← hInter, Set.inter_eq_right.mpr hZsub]
  · intro hEq
    apply hYne.ne_empty
    have hYsub : Y ⊆ Z := by rw [hEq]; exact hUnion ▸ Set.subset_union_left
    rw [← hInter, Set.inter_eq_left.mpr hYsub]

end DomainTheory.NeighbourhoodSystems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_unionCode
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_botCode
import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_left_isScottContinuous
import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_right_isScottContinuous


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

































































theorem valNat_finAux (j : ℕ) : ∀ k,
    valNat (finAux j k) = {n | n < k ∧ j.testBit n} := by
  intro k
  induction k with
  | zero =>
      simp [finAux, valNat_botCode, botElem]
  | succ k ih =>
      simp only [finAux]
      by_cases hk : j.testBit k
      · rw [ite_eq_left hk, valNat_apply, valNat_apply, valNat_unionCode,
          eq_3_12, ih]
        change funOf
          (funOf (lam fun x => graph fun y => x ∪ y) (ofNat k))
          {n | n < k ∧ j.testBit n} =
            {n | n < k + 1 ∧ j.testBit n}
        rw [beta (graph_const_isScottContinuous (fun x y => x ∪ y)
          (fun y => enumerationUnion_left_isScottContinuous y)) (ofNat k)]
        change funOf (lam fun y => ofNat k ∪ y)
          {n | n < k ∧ j.testBit n} =
            {n | n < k + 1 ∧ j.testBit n}
        rw [beta (enumerationUnion_right_isScottContinuous (ofNat k))
          {n | n < k ∧ j.testBit n}]
        ext n
        simp only [Set.mem_union, mem_ofNat, Set.mem_ofPred_eq]
        constructor
        · rintro (hnk | ⟨hn, hb⟩)
          · subst n
            exact ⟨by omega, hk⟩
          · exact ⟨Nat.lt_succ_of_lt hn, hb⟩
        · rintro ⟨hn, hb⟩
          by_cases hnk : n = k
          · exact Or.inl hnk
          · exact Or.inr ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) hnk, hb⟩
      · rw [ite_eq_right hk, ih]
        ext n
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hn, hb⟩
          exact ⟨Nat.lt_succ_of_lt hn, hb⟩
        · rintro ⟨hn, hb⟩
          have hne : n ≠ k := by
            intro hnk
            subst n
            exact hk hb
          exact ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) hne, hb⟩

end DomainTheory.DataTypesAsLattices

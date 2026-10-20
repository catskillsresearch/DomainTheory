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
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_comp_primrec
import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum_range_re
import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum_range_not_computable
import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillCase1Code
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase1Code


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






























theorem theorem_3_5_case1 {u : Pomega} {p : ℕ → ℕ} {n k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : IsExtensional valNat p)
    (hk : k ∈ valNat (p n))
    (hnin : ¬∃ j, e j ⊆ valNat n ∧ k ∈ valNat (p (fin j)))
    (_hinf : ¬(valNat n).Finite) : False := by
  have hiff : ∀ m,
      k ∈ valNat (p (myhillCase1Code n m)) ↔ ¬∃ t, haltEnum t = m := by
    intro m
    by_cases hex : ∃ t, haltEnum t = m
    · have hfin : ({j | ∀ i ≤ j, haltEnum i ≠ m} : Pomega).Finite :=
        (Set.finite_Iio hex.choose).subset fun j hj =>
          Nat.lt_of_not_ge fun hle => hj hex.choose hle hex.choose_spec
      have hfins : (valNat (myhillCase1Code n m)).Finite := by
        rw [valNat_myhillCase1Code]
        exact hfin.inter_of_right _
      obtain ⟨j, hj⟩ := exists_code_of_finite hfins
      have hje : e j ⊆ valNat n := by
        rw [hj, valNat_myhillCase1Code]
        exact Set.inter_subset_left
      have : k ∉ valNat (p (fin j)) := fun h => hnin ⟨j, hje, h⟩
      have heq := hext (myhillCase1Code n m) (fin j) (by simp [hj, valNat_fin])
      simp [heq, this, hex]
    · have hall : {j | ∀ i ≤ j, haltEnum i ≠ m} = Set.univ := by
        ext j
        constructor
        · intro _; trivial
        · intro _ i _
          exact fun h => hex ⟨i, h⟩
      have : valNat (myhillCase1Code n m) = valNat n := by
        rw [valNat_myhillCase1Code, hall]
        simp
      have heq := hext (myhillCase1Code n m) n this
      simp [heq, hk, hex]
  have hre : REPred fun m => ¬∃ t, haltEnum t = m :=
    _root_.REPred.of_eq
      (valNat_mem_comp_primrec (k := k) hu hr (primrec_myhillCase1Code n))
      fun m => hiff m
  exact haltEnum_range_not_computable
    ((ComputablePred.computable_iff_re_compl_re').2 ⟨haltEnum_range_re, hre⟩)

end DomainTheory.DataTypesAsLattices

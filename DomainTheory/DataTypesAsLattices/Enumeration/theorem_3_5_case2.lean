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
import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin
import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillCase2Code
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code_ne_bot
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_comp_primrec


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem theorem_3_5_case2 {u : Pomega} {p : ℕ → ℕ} {n j k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : IsExtensional valNat p)
    (hj : e j ⊆ valNat n)
    (_hne : e j ≠ valNat n)
    (hkfin : k ∈ valNat (p (fin j)))
    (hkn : k ∉ valNat (p n)) : False := by
  have hiff : ∀ m, k ∈ valNat (p (myhillCase2Code j n m)) ↔ valNat m = botElem := by
    intro m
    by_cases hm : valNat m = botElem
    · have : valNat (myhillCase2Code j n m) = e j := by
        rw [valNat_myhillCase2Code, hm, eq_2_7_bot]
        simp [botElem]
      have := hext (myhillCase2Code j n m) (fin j) (by simp [this, valNat_fin])
      simp [this, hkfin, hm]
    · have : valNat (myhillCase2Code j n m) = valNat n :=
        valNat_myhillCase2Code_ne_bot j n m hj hm
      have := hext (myhillCase2Code j n m) n this
      simp [this, hkn, hm]
  have hre : REPred fun m => valNat m = botElem :=
    _root_.REPred.of_eq
      (valNat_mem_comp_primrec (k := k) hu hr (primrec_myhillCase2Code j n))
      fun m => hiff m
  exact theorem_3_4 hre

end DomainTheory.DataTypesAsLattices

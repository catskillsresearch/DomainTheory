/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.subC_realizes2
import DomainTheory.DataTypesAsLattices.Computability.isZeroC_zero
import DomainTheory.DataTypesAsLattices.Computability.isZeroC_succ


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4















theorem leC_realizes2 (n m : ℕ) :
    funOf (funOf leC (ofNat n)) (ofNat m) =
      ofNat (if n ≤ m then 1 else 0) := by
  unfold leC
  rw [Scomb_beta3, Kcomb_beta2, Scomb_beta3, Kcomb_beta2, subC_realizes2]
  by_cases h : n ≤ m
  · have : n - m = 0 := Nat.sub_eq_zero_of_le h
    simp [h, this, isZeroC_zero]
  · have : 0 < n - m := Nat.sub_pos_of_lt (Nat.not_le.mp h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this.ne'
    simp [h, hk, isZeroC_succ]

end DomainTheory.DataTypesAsLattices

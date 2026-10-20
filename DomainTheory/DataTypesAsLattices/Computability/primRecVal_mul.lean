/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.addC_realizes2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4













theorem primRecVal_mul (k : ℕ) : ∀ n,
    primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) n = ofNat (k * n)
  | 0 => by simp [primRecVal]
  | n + 1 => by
    calc primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) (n + 1)
        = funOf (funOf (funOf Kcomb (funOf addC (ofNat k))) (ofNat n))
            (primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) n) :=
          rfl
      _ = funOf (funOf addC (ofNat k))
            (ofNat (k * n)) := by
          rw [Kcomb_beta2, primRecVal_mul k n]
      _ = ofNat (k + k * n) := addC_realizes2 k (k * n)
      _ = ofNat (k * (n + 1)) := by rw [Nat.mul_succ, Nat.add_comm]

end DomainTheory.DataTypesAsLattices

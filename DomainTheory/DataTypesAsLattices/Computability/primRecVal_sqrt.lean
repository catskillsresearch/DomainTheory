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
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

























theorem primRecVal_sqrt (n : ℕ) : ∀ k,
    primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k = ofNat (sqrtIter n k)
  | 0 => rfl
  | k + 1 => by
      rw [show primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) (k + 1) =
        ((sqrtStepC ⬝ ofNat n) ⬝ ofNat k) ⬝
          primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k by rfl,
        primRecVal_sqrt n k, sqrtStepC_app]
      rfl

end DomainTheory.DataTypesAsLattices

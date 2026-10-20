/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12
public import DomainTheory.DataTypesAsLattices.Enumeration.filterC_app
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_filterOp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code





























theorem valNat_myhillFilterCode (m : ℕ) :
    valNat (myhillFilterCode m) = {j | ∀ i ≤ j, haltEnum i ≠ m} := by
  rw [myhillFilterCode, valNat_apply, valNat_filterOp, eq_3_12, filterC_app]

end DomainTheory.DataTypesAsLattices

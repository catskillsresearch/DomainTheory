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
public import DomainTheory.DataTypesAsLattices.Enumeration.condSet_same
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem valNat_myhillCase2Code_ne_bot (j n m : ℕ)
    (hj : e j ⊆ valNat n) (hm : valNat m ≠ botElem) :
    valNat (myhillCase2Code j n m) = valNat n := by
  rw [valNat_myhillCase2Code, condSet_same _ _ hm]
  exact Set.union_eq_self_of_subset_left hj

end DomainTheory.DataTypesAsLattices

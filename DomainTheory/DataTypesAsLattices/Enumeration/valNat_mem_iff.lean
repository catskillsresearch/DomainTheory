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
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_sound
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_complete

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valNat_mem_iff (code member : ℕ) :
    member ∈ valNat code ↔ ∃ tr, valTraceOk tr ∧ valTraceHas tr code member :=
  ⟨valTraceOk_complete code member, fun ⟨_tr, hok, ⟨_t, ht⟩⟩ =>
    valTraceOk_sound hok ht⟩

end DomainTheory.DataTypesAsLattices

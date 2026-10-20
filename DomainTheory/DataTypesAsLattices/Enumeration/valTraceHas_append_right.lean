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

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valTraceHas_append_right {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₂ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inr ht)⟩

end DomainTheory.DataTypesAsLattices

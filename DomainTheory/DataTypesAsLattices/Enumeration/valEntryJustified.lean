/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valEntryJustified (tr : ValTrace) (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 = 0 ∨
    (valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) ∧
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i)

end DomainTheory.DataTypesAsLattices

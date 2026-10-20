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








































theorem enumBottomTerm_avoids (i : ℕ) : enumBottomTerm.Avoids i := by
  unfold enumBottomTerm
  constructor <;>
    (by_cases h : 9 = i
     · exact Or.inl h
     · exact Or.inr ⟨h, h⟩)

end DomainTheory.DataTypesAsLattices

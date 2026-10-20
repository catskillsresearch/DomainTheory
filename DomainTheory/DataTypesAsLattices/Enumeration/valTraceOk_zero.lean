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









theorem valTraceOk_zero (m : ℕ) (hm : m ∈ Gcomb) :
    valTraceOk [(0, m, 0)] ∧ valTraceHas [(0, m, 0)] 0 m := by
  refine ⟨⟨?_, ?_⟩, ⟨0, by simp⟩⟩
  · intro e he
    simp at he
    subst e
    exact Or.inl rfl
  · intro e he he0
    simp at he
    subst e
    exact hm

end DomainTheory.DataTypesAsLattices

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











theorem realizes_valNat_mem {u : Pomega} {p : ℕ → ℕ} (hr : Realizes u p) (n m : ℕ) :
    m ∈ valNat (p n) ↔ ∃ c, c ∈ funOf u (ofNat n) ∧ m ∈ valNat c := by
  rw [hr]
  constructor
  · intro hm
    exact ⟨p n, rfl, hm⟩
  · intro ⟨c, hc, hm⟩
    simp [ofNat] at hc
    subst hc
    exact hm

end DomainTheory.DataTypesAsLattices

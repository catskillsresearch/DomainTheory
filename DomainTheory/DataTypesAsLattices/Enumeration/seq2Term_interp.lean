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
public import DomainTheory.DataTypesAsLattices.Enumeration.enumBottomTerm_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.interp_avoids

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









































theorem seq2Term_interp (a b : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 8) (hb : b.Avoids 8) :
    interp (seq2Term a b) ρ = seq2 (interp a ρ) (interp b ρ) := by
  unfold seq2Term seq2
  apply congrArg graph
  funext z
  simp only [interp]
  rw [interp_avoids a ρ z ha, interp_avoids b ρ z hb, enumBottomTerm_interp]
  simp [envSet, Function.update]

end DomainTheory.DataTypesAsLattices

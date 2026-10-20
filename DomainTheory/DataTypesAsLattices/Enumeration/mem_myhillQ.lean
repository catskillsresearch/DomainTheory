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
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp_eq

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem mem_myhillQ (f : ℕ → ℕ) (k : ℕ) :
    k ∈ myhillQ valNat f ↔
      (unpairComp k).2 ∈ valNat (f (fin (unpairComp k).1)) := by
  constructor
  · intro ⟨j, m, hk, hm⟩
    have : unpairComp k = (j, m) := by
      rw [unpairComp_eq, hk, unpair_pair]
    simpa [this] using hm
  · intro hm
    refine ⟨(unpairComp k).1, (unpairComp k).2, ?_, hm⟩
    rw [unpairComp_eq, pair_unpair]

end DomainTheory.DataTypesAsLattices

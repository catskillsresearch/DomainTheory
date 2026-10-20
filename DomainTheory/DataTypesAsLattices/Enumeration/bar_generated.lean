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
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code




















































theorem bar_generated {u : Pomega} (hu : GeneratedFromG u) :
    GeneratedSemigroup (funOf barComb u) := by
  induction hu with
  | G => exact GeneratedSemigroup.Gbar
  | app _ _ ihu ihv =>
      rw [← eq_3_17]
      exact .comp ihu (.comp ihv .R)

end DomainTheory.DataTypesAsLattices

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
public import DomainTheory.DataTypesAsLattices.Enumeration.barStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.barStep_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- **Scott 1976, (3.15).** Unfolding of the least bar combinator. -/
theorem eq_3_15 (u : Pomega) :
    funOf barComb u = graph (fun x => barStepBody barComb u x) := by
  have hfix : barStep barComb = barComb :=
    (theorem_1_4 barStep_isScottContinuous).1
  have ha := barStep_app barComb u
  rwa [hfix] at ha

end DomainTheory.DataTypesAsLattices

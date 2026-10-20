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
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- **Scott 1976, (3.16).** `L ∘ ū ∘ R = λx. u(x)` from the Y-definition. -/
theorem eq_3_16_bar (u x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x := by
  rw [barComb_app2, barStepBody, Rcomb_app_zero, eq_2_7_zero]
  exact eq_3_16 u x

end DomainTheory.DataTypesAsLattices

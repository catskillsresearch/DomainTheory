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
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_on_R
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_on_barPos_R

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































/-- **Scott 1976, (3.17).** Operator identity
`ū ∘ v̄ ∘ R = overline{u(v)}`. -/
theorem eq_3_17 (u v : Pomega) :
    enumComp (funOf barComb u) (enumComp (funOf barComb v) Rcomb) =
      funOf barComb (funOf u v) := by
  conv_rhs => rw [eq_3_15]
  unfold enumComp
  apply congrArg graph
  funext x
  change funOf (funOf barComb u)
    (funOf (lam fun x => funOf (funOf barComb v) (funOf Rcomb x)) x) =
      barStepBody barComb (funOf u v) x
  rw [beta (theorem_1_3 (funOf_isScottContinuous (funOf barComb v))
      (funOf_isScottContinuous Rcomb)) x]
  rw [barComb_on_R, barComb_on_barPos_R, barComb_app2]

end DomainTheory.DataTypesAsLattices

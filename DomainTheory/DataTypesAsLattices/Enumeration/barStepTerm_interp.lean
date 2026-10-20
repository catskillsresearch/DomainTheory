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
public import DomainTheory.DataTypesAsLattices.Enumeration.barPosTerm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code
















































theorem barStepTerm_interp :
    interp barStepTerm (fun _ => botElem) = graph barStep := by
  unfold barStepTerm barStep
  simp only [interp, envSet, Function.update_self]
  apply congrArg graph
  funext B
  apply congrArg graph
  funext u
  apply congrArg graph
  funext x
  simp [barStepBody, barPosTerm_interp, Function.update,
    succSet_ofNat]

end DomainTheory.DataTypesAsLattices

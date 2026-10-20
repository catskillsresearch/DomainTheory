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
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecPred_valTraceStruct
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceG_re

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem valTraceOk_re : REPred valTraceOk :=
  _root_.REPred.of_eq
    (REPred.and primrecPred_valTraceStruct.computablePred.to_re valTraceG_re)
    fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices

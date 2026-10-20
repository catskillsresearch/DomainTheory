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
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.seqCons_right_isScottContinuous

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barPos_isScottContinuous_x (u : Pomega) :
    IsScottContinuous (fun x => barPos u x) :=
  theorem_1_3 (f := fun xs => seqCons (ofNat 1) xs)
    (g := fun x => seq2 u (funOf x (ofNat 1)))
    (seqCons_right_isScottContinuous (ofNat 1))
    (theorem_1_3 (seq2_right_isScottContinuous u)
      (funOf_isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices

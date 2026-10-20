/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.barPos_isScottContinuous_u


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barStepBody_isScottContinuous_u (B x : Pomega) :
    IsScottContinuous (fun u => barStepBody B u x) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid (funOf x (ofNat 0)) y)
    (fun w => condSet_isScottContinuous_right (funOf x (ofNat 0)) w)
    (barPos_isScottContinuous_u x)
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun u => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (theorem_1_3 (funOf_isScottContinuous B)
        (funOf_isScottContinuous_left (funOf x (ofNat 1)))))

end DomainTheory.DataTypesAsLattices

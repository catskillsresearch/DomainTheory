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
import DomainTheory.DataTypesAsLattices.Enumeration.seq2_left_isScottContinuous
import DomainTheory.DataTypesAsLattices.Enumeration.seqCons_right_isScottContinuous


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













































theorem barPos_isScottContinuous_u (x : Pomega) :
    IsScottContinuous (fun u => barPos u x) :=
  theorem_1_3 (seqCons_right_isScottContinuous (ofNat 1))
    (seq2_left_isScottContinuous (funOf x (ofNat 1)))

end DomainTheory.DataTypesAsLattices

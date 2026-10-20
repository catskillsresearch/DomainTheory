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
import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody_isScottContinuous_x
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































theorem barComb_app2 (u x : Pomega) :
    funOf (funOf barComb u) x = barStepBody barComb u x := by
  have ha : funOf barComb u = graph (fun z => barStepBody barComb u z) :=
    eq_3_15 u
  rw [ha]
  exact beta (barStepBody_isScottContinuous_x barComb u) x

end DomainTheory.DataTypesAsLattices

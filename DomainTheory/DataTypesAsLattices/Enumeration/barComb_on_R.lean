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
import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2
import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app_zero


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































theorem barComb_on_R (u x : Pomega) :
    funOf (funOf barComb u) (funOf Rcomb x) =
      barPos u (funOf Rcomb x) := by
  rw [barComb_app2, barStepBody, Rcomb_app_zero, eq_2_7_zero]

end DomainTheory.DataTypesAsLattices

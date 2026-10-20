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
import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app
import DomainTheory.DataTypesAsLattices.Enumeration.barPos_zero
import DomainTheory.DataTypesAsLattices.Enumeration.barPos_one
import DomainTheory.DataTypesAsLattices.Enumeration.barPos_two
import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































theorem barComb_on_barPos_R (u v x : Pomega) :
    funOf (funOf barComb u) (barPos v (funOf Rcomb x)) =
      funOf (funOf barComb (funOf u v)) x := by
  rw [barComb_app2, barStepBody, barPos_zero, eq_2_7_succ,
    barPos_one, barPos_two, Rcomb_app, seq2_app_one]

end DomainTheory.DataTypesAsLattices

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
import DomainTheory.DataTypesAsLattices.Enumeration.barStep_isScottContinuous
import DomainTheory.DataTypesAsLattices.Enumeration.barStep_app


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- **Scott 1976, (3.15).** Unfolding of the least bar combinator. -/
theorem eq_3_15 (u : Pomega) :
    funOf barComb u = graph (fun x => barStepBody barComb u x) := by
  have hfix : barStep barComb = barComb :=
    (theorem_1_4 barStep_isScottContinuous).1
  have ha := barStep_app barComb u
  rwa [hfix] at ha

end DomainTheory.DataTypesAsLattices

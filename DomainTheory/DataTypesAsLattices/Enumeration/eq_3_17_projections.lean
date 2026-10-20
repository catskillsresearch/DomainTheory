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
import DomainTheory.DataTypesAsLattices.Enumeration.barPos_one
import DomainTheory.DataTypesAsLattices.Enumeration.barPos_two


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- Projection calculation used in the proof of Scott 1976, (3.17). -/
theorem eq_3_17_projections (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x := by
  refine ⟨barPos_one _ _, barPos_one _ _, ?_⟩
  rw [barPos_two, Rcomb_app, seq2_app_one]

end DomainTheory.DataTypesAsLattices

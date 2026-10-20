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
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16_bar
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17_projections


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- The pointwise calculations used by Theorem 3.7. -/
theorem theorem_3_7_equations (u v x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x :=
  ⟨eq_3_16_bar u x, (eq_3_17_projections u v x).2.1,
    (eq_3_17_projections u v x).2.2⟩

end DomainTheory.DataTypesAsLattices

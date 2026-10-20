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


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code












theorem condSet_same (z x : Pomega) (hz : z ≠ botElem) : condSet z x x = x := by
  by_cases h0 : 0 ∈ z
  · by_cases hsing : z = ofNat 0
    · subst hsing
      exact eq_2_7_zero x x
    · rw [eq_2_7_mix x x z h0 hsing]
      simp
  · exact eq_2_7_pos x x z h0 hz

end DomainTheory.DataTypesAsLattices

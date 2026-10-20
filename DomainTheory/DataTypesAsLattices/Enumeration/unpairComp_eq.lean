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



theorem unpairComp_eq (k : ℕ) : unpairComp k = unpair k := by
  unfold unpairComp
  set w := Nat.find (exists_triangle_succ k) with hw
  have hlt : k < triangle (w + 1) := by
    simpa [hw] using Nat.find_spec (exists_triangle_succ k)
  have hle : triangle w ≤ k := by
    cases hwc : w with
    | zero => simp [triangle]
    | succ w' =>
      have hlt' : w' < Nat.find (exists_triangle_succ k) := by
        rw [← hw, hwc]
        exact Nat.lt_succ_self w'
      exact Nat.le_of_not_gt (Nat.find_min (exists_triangle_succ k) hlt')
  have hm : k - triangle w ≤ w := by
    have : k < triangle w + (w + 1) := by
      rwa [triangle_succ] at hlt
    omega
  have hpair : pair (w - (k - triangle w)) (k - triangle w) = k := by
    have : w - (k - triangle w) + (k - triangle w) = w := Nat.sub_add_cancel hm
    simp [pair_eq_triangle, this, Nat.add_sub_of_le hle]
  rw [← unpair_pair (w - (k - triangle w)) (k - triangle w), hpair]

end DomainTheory.DataTypesAsLattices

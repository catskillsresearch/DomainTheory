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
import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec_succ


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem unpairWRec_min (k n m : ℕ)
    (hm : m < unpairWRec k n) : ¬k < triangle (m + 1) := by
  induction n generalizing m with
  | zero =>
    simp [unpairWRec] at hm
  | succ n ih =>
    by_cases hk : k < triangle (n + 1)
    · simp [unpairWRec_succ, hk] at hm
      exact ih m hm
    · simp [unpairWRec_succ, hk] at hm
      intro hlt
      have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
      exact hk (lt_of_lt_of_le hlt (triangle_le_of_le (Nat.succ_le_succ hm')))

end DomainTheory.DataTypesAsLattices

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











theorem unpairWRec_lt (k n : ℕ) :
    k < triangle (unpairWRec k n + 1) ∨ unpairWRec k n = n := by
  induction n with
  | zero =>
    by_cases hk : k < triangle 1
    · exact Or.inl (by simp [unpairWRec, hk])
    · exact Or.inr (by simp [unpairWRec])
  | succ n ih =>
    by_cases hk : k < triangle (n + 1)
    · simp [unpairWRec_succ, hk]
      exact ih.elim Or.inl fun heq => Or.inl (by simpa [heq] using hk)
    · simp [unpairWRec_succ, hk]

end DomainTheory.DataTypesAsLattices

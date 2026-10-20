/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec_lt
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec_min

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem unpairW_eq (k : ℕ) : unpairW k = Nat.find (exists_triangle_succ k) := by
  refine ((Nat.find_eq_iff (exists_triangle_succ k)).mpr ⟨?_, fun m hm =>
      unpairWRec_min k k m hm⟩).symm
  rcases unpairWRec_lt k k with h | hrec
  · exact h
  · have : k + 1 ≤ triangle (k + 1) := by
      cases k with
      | zero => simp [triangle]
      | succ k =>
        rw [triangle_succ]
        exact Nat.le_add_left _ _
    simpa [unpairW, hrec] using lt_of_lt_of_le (Nat.lt_succ_self k) this

end DomainTheory.DataTypesAsLattices

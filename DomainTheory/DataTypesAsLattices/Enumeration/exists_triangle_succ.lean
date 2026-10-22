/-ai
For every natural number k there is a natural number w such that k is strictly less than the triangular number of w + 1.

Take w equal to k. Rewrite by the successor equation for triangular numbers. Then k is strictly less than k + 1, and k + 1 is at most the sum of k + 1 with the remaining argument of that equation.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem exists_triangle_succ (k : ℕ) : ∃ w, k < triangle (w + 1) :=
  ⟨k, by
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩

end DomainTheory.DataTypesAsLattices

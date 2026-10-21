/-ai
For every k and n, either k is less than the triangular number one beyond the bounded scan of k for n steps, or that scan equals n.

If n is zero and k is less than the first triangular number, the scan is 0 and the inequality holds; otherwise the scan equals 0. If n is a successor and k is already below the (n + 1)-st triangular number, the successor equation for the scan reduces the claim to the inductive hypothesis, and equality of the earlier scan with n converts the case hypothesis into the desired inequality. If k is not below that triangular number, the successor equation makes the scan equal n + 1.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec_succ

@[expose] public section


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

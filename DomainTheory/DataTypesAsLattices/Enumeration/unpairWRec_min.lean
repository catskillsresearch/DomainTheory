/-ai
If m lies strictly below unpairWRec k n, then k fails to lie strictly below triangle (m + 1).

The proof is by induction on n, with m kept general. At zero the hypothesis contradicts the clause defining unpairWRec. At a successor the argument splits on whether k lies strictly below triangle (n + 1). When it does, the successor equation reduces the hypothesis to the inductive hypothesis. When it does not, that equation gives m at most n, and a supposed bound k < triangle (m + 1) contradicts the case assumption by monotonicity of triangle.
ai-/
module

public import Mathlib.Computability.Halting
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

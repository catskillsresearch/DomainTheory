
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Bounded scan for the least `w` with `k < triangle (w+1)`. -/
def unpairWRec (k n : ℕ) : ℕ :=
  Nat.rec 0 (fun w ih => if k < triangle (w + 1) then ih else w + 1) n

namespace unpairWRec

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem succ (k n : ℕ) :
    unpairWRec k (n + 1) =
      if k < triangle (n + 1) then unpairWRec k n else n + 1 :=
  rfl

theorem lt (k n : ℕ) :
    k < triangle (unpairWRec k n + 1) ∨ unpairWRec k n = n := by
  induction n with
  | zero =>
    by_cases hk : k < triangle 1
    · exact Or.inl (by simp [unpairWRec, hk])
    · exact Or.inr (by simp [unpairWRec])
  | succ n ih =>
    by_cases hk : k < triangle (n + 1)
    · simp [unpairWRec.succ, hk]
      exact ih.elim Or.inl fun heq => Or.inl (by simpa [heq] using hk)
    · simp [unpairWRec.succ, hk]

theorem min (k n m : ℕ)
    (hm : m < unpairWRec k n) : ¬k < triangle (m + 1) := by
  induction n generalizing m with
  | zero =>
    simp [unpairWRec] at hm
  | succ n ih =>
    by_cases hk : k < triangle (n + 1)
    · simp [unpairWRec.succ, hk] at hm
      exact ih m hm
    · simp [unpairWRec.succ, hk] at hm
      intro hlt
      have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
      exact hk (lt_of_lt_of_le hlt (triangle_le_of_le (Nat.succ_le_succ hm')))

end unpairWRec

end DomainTheory.DataTypesAsLattices

/-ai
The iteration sqrtIter n k equals the minimum of k and the integer square root of n.

Induct on k. The zero case is the definition of sqrtIter. At a successor, rewrite by the inductive hypothesis. If k lies strictly below the square root, the minimum is k and (k + 1) · (k + 1) is at most n by Nat.le_sqrt, so the iteration steps to k + 1, the minimum of the successor and the square root. Otherwise the square root is at most k, the minimum is the square root, and the square of one more than the square root fails to be at most n by Nat.lt_succ_sqrt, so the iteration remains at the square root.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4





















theorem sqrtIter_eq_min (n k : ℕ) : sqrtIter n k = min k (Nat.sqrt n) := by
  induction k with
  | zero => simp [sqrtIter]
  | succ k ih =>
    rw [sqrtIter, ih]
    by_cases h : k < Nat.sqrt n
    · have hmin : min k (Nat.sqrt n) = k := min_eq_left h.le
      have hs : (k + 1) * (k + 1) ≤ n := Nat.le_sqrt.mp h
      simp [hmin, hs, min_eq_left (Nat.succ_le_iff.mpr h)]
    · have hk : Nat.sqrt n ≤ k := Nat.le_of_not_gt h
      have hmin : min k (Nat.sqrt n) = Nat.sqrt n := min_eq_right hk
      have hs : ¬(Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n :=
        Nat.not_le.mpr (Nat.lt_succ_sqrt n)
      simp [hmin, hs, min_eq_right (hk.trans (Nat.le_succ k))]

end DomainTheory.DataTypesAsLattices

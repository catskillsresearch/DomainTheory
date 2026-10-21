/-ai
The computable unpairing of k equals Scott's unpairing of k.

Let w be the least number such that k is less than the (w + 1)-st triangular number. Then k lies strictly below that triangular number, and the w-th triangular number is at most k: this is immediate when w is zero, and when w is a successor the minimality of the search excludes every smaller candidate. The difference of k and the w-th triangular number is at most w, because k is less than that triangular number plus w + 1 by the successor equation for triangular numbers. The two components of the computable unpairing therefore sum to w, and the pairing equation shows that their pair equals k. Unpairing that pair recovers the computable unpairing.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


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

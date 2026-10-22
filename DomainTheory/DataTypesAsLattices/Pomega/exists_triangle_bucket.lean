/-ai
Every natural number k lies in a half-open triangular interval: some w has the triangular number of w at most k and k strictly below the triangular number of w + 1.

Let P(w) say that k is strictly below the triangular number of w + 1. This holds at w = k, because the successor law writes the triangular number of k + 1 as the triangular number of k plus k + 1, which is at least k + 1. Let w be the least such number. The upper bound is the specification of that least number. If w is zero, the lower bound is immediate. If w is a successor, its predecessor fails P, so the triangular number of w is at most k.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst11
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst12
public import DomainTheory.DataTypesAsLattices.Pomega.triangle
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_succ

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem exists_triangle_bucket (k : ℕ) :
    ∃ w, triangle w ≤ k ∧ k < triangle (w + 1) := by
  let P := fun w : ℕ => k < triangle (w + 1)
  have hP : ∃ w, P w := ⟨k, by
    change k < triangle (k + 1)
    rw [triangle_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) _)⟩
  let w := Nat.find hP
  refine ⟨w, ?_, Nat.find_spec hP⟩
  cases hw : w with
  | zero => exact Nat.zero_le k
  | succ w' =>
    have hmin : ¬ P w' :=
      Nat.find_min hP (Nat.lt_of_succ_le (by
        have : w = Nat.find hP := rfl
        rw [← this, hw]))
    exact Nat.le_of_not_gt hmin

end DomainTheory.DataTypesAsLattices

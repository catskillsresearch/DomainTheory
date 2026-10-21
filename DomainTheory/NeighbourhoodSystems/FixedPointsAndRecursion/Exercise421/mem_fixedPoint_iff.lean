/-ai
A pair belongs to a fixed point of Scott's operator if and only if its first component is at most its second.

Proceed by induction on the second component, rewriting membership by the fixed-point equation. When the second component is zero, a diagonal pair is ordered by equality, a successor clause cannot make zero a successor, and an inequality with right side zero forces equality, hence the diagonal. At a successor, a diagonal pair is ordered by equality, and a successor witness has predecessor equal to the inductive index, so the inductive hypothesis and the successor of an inequality give the order; conversely equality is the diagonal, and a strict inequality supplies the predecessor pair by the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414




/-- The key step toward uniqueness: any fixed point `u` of `leOp` agrees with `≤` pointwise.
By induction on the second coordinate `m`; the base case `m = 0` uses that the successor clause
cannot produce a `0` on the right. -/
theorem mem_fixedPoint_iff {u : Set (ℕ × ℕ)} (hu : leOp u = u) (n m : ℕ) :
    (n, m) ∈ u ↔ n ≤ m := by
  induction m with
  | zero =>
    rw [← hu]
    constructor
    · rintro (h | ⟨k, _, hk⟩)
      · exact le_of_eq h
      · exact absurd hk (Nat.succ_ne_zero k).symm
    · intro h
      exact Or.inl (Nat.le_zero.mp h)
  | succ k ih =>
    rw [← hu]
    constructor
    · rintro (h | ⟨j, hj, hjk⟩)
      · exact le_of_eq h
      · have hjk' : j = k := by omega
        subst hjk'
        exact Nat.le_succ_of_le (ih.mp hj)
    · intro h
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨k, ih.mpr (Nat.lt_succ_iff.mp h'), rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise421

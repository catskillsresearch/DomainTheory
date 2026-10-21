/-ai
The least fixed point of the multiplication operator of n is the set of multiples of n.

The multiples form a pre-fixed point, since zero is the multiple of index zero and n plus the multiple of index i is the multiple of index i + 1, so the least fixed point is contained in the multiples. Conversely, each multiple of index i lies in the least fixed point by induction on i, using that the least fixed point is fixed: the multiple of index zero is the zero clause, and the next multiple is the sum clause applied to the inductive multiple.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.mulOp_monotone

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_isFixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_subset
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414


/-- **Exercise 4.21 (Scott 1981, PRG-19).** The least solution of the multiplication equation
`n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` is exactly the set of **multiples of `n`**. -/
theorem mulOp_lfp_eq_multiples (n : ℕ) :
    lfpSet (mulOp n) = {k | ∃ i, k = n * i} := by
  apply Set.Subset.antisymm
  · -- `lfpSet ⊆ multiples`: the multiples form a pre-fixed point.
    have hpre : mulOp n {k | ∃ i, k = n * i} ⊆ {k | ∃ i, k = n * i} := by
      rintro k (rfl | ⟨m, ⟨i, rfl⟩, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by ring⟩
    exact lfpSet_subset (mulOp n) hpre
  · -- `multiples ⊆ lfpSet`: each `n * i` is reached by induction on `i`.
    have hfix : mulOp n (lfpSet (mulOp n)) = lfpSet (mulOp n) :=
      lfpSet_isFixed (mulOp n) (mulOp_monotone n)
    rintro k ⟨i, rfl⟩
    induction i with
    | zero =>
      rw [← hfix]; exact Or.inl (by simp)
    | succ j ih =>
      rw [← hfix]
      exact Or.inr ⟨n * j, ih, by ring⟩

end DomainTheory.NeighbourhoodSystems.Exercise421

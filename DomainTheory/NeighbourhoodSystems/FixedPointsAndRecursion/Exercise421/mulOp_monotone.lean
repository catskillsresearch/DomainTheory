/-ai
For each natural n, the multiplication operator is monotone.

The zero clause is unchanged. A sum witness in the smaller set is a sum witness in the larger set by the assumed inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414


theorem mulOp_monotone (n : ℕ) : Monotone (mulOp n) := by
  rintro u v huv k (hk | ⟨m, hm, rfl⟩)
  · exact Or.inl hk
  · exact Or.inr ⟨m, huv hm, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise421

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leRel
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.succImage
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.addIso
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.mulOp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414


theorem mulOp_monotone (n : ℕ) : Monotone (mulOp n) := by
  rintro u v huv k (hk | ⟨m, hm, rfl⟩)
  · exact Or.inl hk
  · exact Or.inr ⟨m, huv hm, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise421

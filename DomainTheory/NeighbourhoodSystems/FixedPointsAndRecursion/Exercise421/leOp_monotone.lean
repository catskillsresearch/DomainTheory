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


theorem leOp_monotone : Monotone leOp := by
  intro u v huv p hp
  rcases hp with hp | ⟨m, hm, hpm⟩
  · exact Or.inl hp
  · exact Or.inr ⟨m, huv hm, hpm⟩

end DomainTheory.NeighbourhoodSystems.Exercise421

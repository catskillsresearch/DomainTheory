module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp_monotone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_isFixed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbSet_isFixed (f : A → B) (g : B → A) : sbOp f g (sbSet f g) = sbSet f g :=
  lfpSet_isFixed (sbOp f g) (sbOp_monotone f g)

end DomainTheory.NeighbourhoodSystems.Exercise424

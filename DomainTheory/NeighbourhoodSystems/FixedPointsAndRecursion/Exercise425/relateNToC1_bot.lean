module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `relateNToC1(⊥) = ⊥`. -/
theorem relateNToC1_bot : relateNToC1.toElementMap Example43.N.bot = C1.bot :=
  Example43.constLiftN_bot C1 oneElem

end DomainTheory.NeighbourhoodSystems.Exercise425

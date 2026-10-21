/-ai
The predecessor sends the total element at zero to bottom.

This is the computation rule of the constant lift on total elements, applied to the predecessor table at zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN_natElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap






















/-- `pred(0̂) = ⊥`: predecessor of zero is undefined. -/
theorem predMap_natElem_zero : predMap.toElementMap (natElem 0) = N.bot :=
  constLiftN_natElem N predVal 0

end DomainTheory.NeighbourhoodSystems.Example43

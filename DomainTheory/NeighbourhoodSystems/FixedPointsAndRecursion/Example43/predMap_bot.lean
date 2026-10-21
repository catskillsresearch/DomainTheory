/-ai
The predecessor sends bottom to bottom.

This is the strictness rule of the constant lift, applied to the predecessor table.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `pred(⊥) = ⊥`. -/
theorem predMap_bot : predMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N predVal

end DomainTheory.NeighbourhoodSystems.Example43

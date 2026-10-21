/-ai
The successor sends bottom to bottom.

This is the strictness rule of the constant lift, applied to the successor values.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap



















/-- `succ(⊥) = ⊥`. -/
theorem succMap_bot : succMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N (fun n => natElem (n + 1))

end DomainTheory.NeighbourhoodSystems.Example43

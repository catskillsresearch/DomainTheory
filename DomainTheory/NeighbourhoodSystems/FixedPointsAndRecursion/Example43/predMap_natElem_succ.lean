module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN_natElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `pred((n+1)^) = n̂`. -/
theorem predMap_natElem_succ (k : ℕ) : predMap.toElementMap (natElem (k + 1)) = natElem k :=
  constLiftN_natElem N predVal (k + 1)

end DomainTheory.NeighbourhoodSystems.Example43

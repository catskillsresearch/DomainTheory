module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.succMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_ne_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_nat_inj
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN_natElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `succ(n̂) = (n+1)^`. -/
theorem succMap_natElem (n : ℕ) : succMap.toElementMap (natElem n) = natElem (n + 1) :=
  constLiftN_natElem N (fun n => natElem (n + 1)) n

end DomainTheory.NeighbourhoodSystems.Example43

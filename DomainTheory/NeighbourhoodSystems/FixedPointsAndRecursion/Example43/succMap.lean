module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Example 4.3 — `succ`.** `succ(n) = n + 1`, strict (`succ(⊥) = ⊥`). -/
def succMap : ApproximableMap N N := constLiftN N (fun n => natElem (n + 1))

end DomainTheory.NeighbourhoodSystems.Example43

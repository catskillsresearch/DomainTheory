/-ai
The predecessor table sends zero to bottom and sends k + 1 to the total element at k.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The value table for `pred`: `pred(0) = ⊥`, `pred(k+1) = k`. -/
def predVal : ℕ → N.Element
  | 0 => N.bot
  | (k + 1) => natElem k

end DomainTheory.NeighbourhoodSystems.Example43

/-ai
The zero table sends zero to the true element of the truth domain and sends every successor to the false element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.T

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The value table for `zero`: `zero(0) = true`, `zero(n+1) = false`. -/
def zeroVal : ℕ → T.Element
  | 0 => Example23.trueElt
  | (_ + 1) => Example23.falseElt

end DomainTheory.NeighbourhoodSystems.Example43

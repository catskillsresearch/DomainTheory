/-ai
The zero test sends the total element at n + 1 to false.

This is the computation rule of the constant lift on total elements, applied to the zero table at n + 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN_natElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- `zero((n+1)^) = false`. -/
theorem zeroMap_natElem_succ (n : ℕ) : zeroMap.toElementMap (natElem (n + 1)) = Example23.falseElt :=
  constLiftN_natElem T zeroVal (n + 1)

end DomainTheory.NeighbourhoodSystems.Example43

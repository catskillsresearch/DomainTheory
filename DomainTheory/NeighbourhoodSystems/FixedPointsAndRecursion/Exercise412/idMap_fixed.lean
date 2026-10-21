/-ai
Every element of the domain of Example 1.2 is a fixed point of the identity map.

The elementwise action of the identity map is the identity on elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem


/-- **Exercise 4.12 (Scott 1981, PRG-19).** Every element is a fixed point of the identity map
(so `I_T` has *many* fixed points: `⊥`, `elemZero`, `elemOne`). -/
theorem idMap_fixed (x : T.Element) : (idMap T).toElementMap x = x := toElementMap_idMap x

end DomainTheory.NeighbourhoodSystems.Exercise412

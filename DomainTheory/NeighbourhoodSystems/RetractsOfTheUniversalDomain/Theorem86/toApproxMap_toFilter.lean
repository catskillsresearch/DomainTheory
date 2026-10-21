/-ai
Extracting the approximable map of the filter of a map recovers the map.

This is the right inverse of the function-space equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_toFilter (f : ApproximableMap E E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv E E).right_inv f

end Sub8_6

end DomainTheory.NeighbourhoodSystems

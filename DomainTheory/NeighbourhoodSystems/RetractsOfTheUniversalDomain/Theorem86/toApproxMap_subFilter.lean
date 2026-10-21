/-ai
Extracting the approximable map of the filter transport of an element recovers sub of the map extracted from that element.

Extraction after passage to a filter is the identity on approximable maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_subFilter (φ : (funSpace E E).Element) :
    toApproxMap (subFilter φ) = sub (toApproxMap φ) :=
  toApproxMap_toFilter _

end Sub8_6

end DomainTheory.NeighbourhoodSystems

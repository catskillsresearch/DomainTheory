/-ai
The element map of the packaged map subApprox is the filter transport of sub.

This is the element map of the continuous packaging of that transport.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.continuous_subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subApprox

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.toElementMap_ofContinuous
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toElementMap_subApprox (φ : (funSpace E E).Element) :
    subApprox.toElementMap φ = subFilter φ :=
  toElementMap_ofContinuous subFilter continuous_subFilter φ

end Sub8_6

end DomainTheory.NeighbourhoodSystems

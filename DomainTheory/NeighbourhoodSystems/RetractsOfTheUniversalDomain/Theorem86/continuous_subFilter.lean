/-ai
The filter transport of sub is continuous.

Continuity follows from monotonicity together with preservation of directed suprema.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter_iSupDirected
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter_monotone

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213.continuous_of_monotone_iSupDirected
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`subFilter` is (topologically) continuous**, via the domain-theoretic bridge
`continuous_of_monotone_iSupDirected` (monotone + preserves directed unions). -/
theorem continuous_subFilter : Continuous (subFilter (E := E)) :=
  continuous_of_monotone_iSupDirected subFilter_monotone subFilter_iSupDirected

end Sub8_6

end DomainTheory.NeighbourhoodSystems

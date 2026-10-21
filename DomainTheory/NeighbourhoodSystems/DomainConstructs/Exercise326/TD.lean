/-ai
The truth domain is the neighbourhood system of Example 1.2, whose neighbourhoods are the master set, the singleton of zero, and the singleton of one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- The truth domain `T` of Example 1.2 (neighbourhoods `{Δ, {0}, {1}}`). -/
abbrev TD : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Exercise326

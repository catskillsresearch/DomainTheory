module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- The truth domain `T` of Example 1.2 (neighbourhoods `{Δ, {0}, {1}}`). -/
abbrev TD : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Exercise326

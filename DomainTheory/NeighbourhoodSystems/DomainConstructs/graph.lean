/-ai
The graph of an approximable map is the set of neighbourhood pairs that the map relates.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The **graph** of an approximable map, as a set of neighbourhood pairs. -/
def graph (f : ApproximableMap V₀ V₁) : Set (Set α × Set β) := {p | f.rel p.1 p.2}

end DomainTheory.NeighbourhoodSystems.Exercise327

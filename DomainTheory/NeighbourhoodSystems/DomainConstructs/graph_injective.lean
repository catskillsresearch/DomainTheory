/-ai
The graph of an approximable map determines the map.

If two graphs are equal as sets, then every neighbourhood pair belongs to one if and only if it belongs to the other, so the relations agree and the maps are equal by extensionality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem graph_injective : Function.Injective (graph (V₀ := V₀) (V₁ := V₁)) :=
  fun _ _ h => ApproximableMap.ext fun X Y => Set.ext_iff.mp h (X, Y)

end DomainTheory.NeighbourhoodSystems.Exercise327

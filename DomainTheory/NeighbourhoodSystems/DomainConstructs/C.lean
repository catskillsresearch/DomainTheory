/-ai
Scott's family C of two neighbourhood systems is the set of graphs of approximable maps from the first system to the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's family `C`: all graphs of approximable maps `𝒟₀ → 𝒟₁`. -/
def C (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Set (Set (Set α × Set β)) :=
  Set.range (graph (V₀ := V₀) (V₁ := V₁))

end DomainTheory.NeighbourhoodSystems.Exercise327

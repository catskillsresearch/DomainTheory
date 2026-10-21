/-ai
A pair of sets belongs to the graph of an approximable map if and only if the map relates the first component to the second.

The two sides are the same by the definition of the graph.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_graph {f : ApproximableMap V₀ V₁} {p : Set α × Set β} :
    p ∈ graph f ↔ f.rel p.1 p.2 := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise327

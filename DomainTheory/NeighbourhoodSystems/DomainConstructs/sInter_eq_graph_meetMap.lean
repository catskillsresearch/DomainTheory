/-ai
The intersection of a nonempty family of graphs of approximable maps equals the graph of the meet of that family.

After unfolding membership in an intersection and membership in a graph, each direction says that the pair belongs to every member of the family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.meetMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sInter_eq_graph_meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) : ⋂₀ 𝒮 = graph (meetMap 𝒮 h𝒮 hne) := by
  ext p
  simp only [Set.mem_sInter, mem_graph]
  exact ⟨fun h S hS => h S hS, fun h S hS => h S hS⟩

end DomainTheory.NeighbourhoodSystems.Exercise327

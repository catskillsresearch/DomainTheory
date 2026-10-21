/-ai
The union of a nonempty directed family of graphs of approximable maps equals the graph of the join of that family.

After unfolding membership in a union and membership in a graph, each direction is the existence of a member of the family that contains the pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.joinMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sUnion_eq_graph_joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) (hdir : DirectedOn (· ⊆ ·) 𝒮) :
    ⋃₀ 𝒮 = graph (joinMap 𝒮 h𝒮 hne hdir) := by
  ext p
  simp only [Set.mem_sUnion, mem_graph]
  exact ⟨fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩, fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise327

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.joinMap

@[expose] public section

set_option linter.unusedSectionVars false

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

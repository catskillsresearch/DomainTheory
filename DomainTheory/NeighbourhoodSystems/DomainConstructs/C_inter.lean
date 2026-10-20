module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.meetMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sInter_eq_graph_meetMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.22 hypothesis (i).** `C` is closed under non-empty intersections. -/
theorem C_inter : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ → ⋂₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮
  rw [sInter_eq_graph_meetMap 𝒮 h𝒮 hne]
  exact ⟨meetMap 𝒮 h𝒮 hne, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise327

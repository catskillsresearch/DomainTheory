module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `graph` is an order-isomorphism of approximable maps (under `⊑`) onto the family `C`
(under `⊆`). -/
noncomputable def graphEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ V₁ ≃o {X : Set (Set α × Set β) // X ∈ C V₀ V₁} where
  toFun f := ⟨graph f, f, rfl⟩
  invFun X := X.2.choose
  left_inv f := graph_injective (⟨graph f, f, rfl⟩ : {X // X ∈ C V₀ V₁}).2.choose_spec
  right_inv X := Subtype.ext X.2.choose_spec
  map_rel_iff' := by
    intro f g
    show graph f ⊆ graph g ↔ f ≤ g
    rw [ApproximableMap.le_iff]
    exact ⟨fun h X Y hf => h (a := (X, Y)) hf, fun h p hp => h p.1 p.2 hp⟩

end DomainTheory.NeighbourhoodSystems.Exercise327

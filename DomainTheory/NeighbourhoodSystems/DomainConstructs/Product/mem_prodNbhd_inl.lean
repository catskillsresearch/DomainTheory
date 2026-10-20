module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem mem_prodNbhd_inl {X : Set α} {Y : Set β} {a : α} :
    (Sum.inl a : α ⊕ β) ∈ prodNbhd X Y ↔ a ∈ X := by
  simp [prodNbhd]

end DomainTheory.NeighbourhoodSystems

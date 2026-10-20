module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

@[simp] theorem mem_prodNbhd_inr {X : Set α} {Y : Set β} {b : β} :
    (Sum.inr b : α ⊕ β) ∈ prodNbhd X Y ↔ b ∈ Y := by
  simp [prodNbhd]

end DomainTheory.NeighbourhoodSystems

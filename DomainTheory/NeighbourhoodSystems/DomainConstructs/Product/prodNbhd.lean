module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- The product neighbourhood `X ∪ Y` over the disjoint union `Δ₀ ∪ Δ₁`, modelled on `α ⊕ β` as
`Sum.inl '' X ∪ Sum.inr '' Y`. -/
def prodNbhd (X : Set α) (Y : Set β) : Set (α ⊕ β) := Sum.inl '' X ∪ Sum.inr '' Y

end DomainTheory.NeighbourhoodSystems

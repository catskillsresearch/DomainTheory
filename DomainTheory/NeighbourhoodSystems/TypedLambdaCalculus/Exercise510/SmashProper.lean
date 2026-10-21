/-ai
A set is a proper product neighbourhood of the smash product when it is the product neighbourhood of a neighbourhood of the first system other than its master and a neighbourhood of the second system other than its master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

/-- A *proper* product neighbourhood of the smash: `X ∪ Y` with `X ∈ 𝒟₀ ∖ {Δ₀}` and
`Y ∈ 𝒟₁ ∖ {Δ₁}` (both factors strictly below their masters). -/
def SmashProper (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (W : Set (α ⊕ β)) : Prop :=
  ∃ X Y, V₀.mem X ∧ X ≠ V₀.master ∧ V₁.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y

end DomainTheory.NeighbourhoodSystems.Exercise510

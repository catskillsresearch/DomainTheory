/-ai
The least single-step map from a neighbourhood Y to a neighbourhood Z is the least approximable map of the one-element list containing the pair of Y and Z. The only pair on that list is this pair of neighbourhoods, and consistency of the list is consistency of a single step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.stepCons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The single-step least map `f₀ ∈ [Y, Z]`: `leastMap [(Y, Z)]`, the minimal approximable mapping
relating `Y` to `Z`. -/
def leastStep (Y : Set α) (Z : Set β) (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    ApproximableMap V₀ V₁ :=
  leastMap [(Y, Z)] (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)

end DomainTheory.NeighbourhoodSystems

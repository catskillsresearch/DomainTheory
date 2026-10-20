module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-- The tagged left copy `0X`. -/
def j0 {α β γ : Type*} (X : Set α) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ a, w = t0 a ∧ a ∈ X}

end DomainTheory.NeighbourhoodSystems

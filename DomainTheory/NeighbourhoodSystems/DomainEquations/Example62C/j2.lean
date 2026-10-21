/-ai
The tagged right copy of a set Z of elements of γ is the set of tokens t2 c, in Option (α ⊕ β ⊕ γ), for which c lies in Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-- The tagged right copy `2Z`. -/
def j2 {α β γ : Type*} (Z : Set γ) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ c, w = t2 c ∧ c ∈ Z}

end DomainTheory.NeighbourhoodSystems

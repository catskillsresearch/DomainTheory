module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-- The tagged middle copy `1Y`. -/
def j1 {α β γ : Type*} (Y : Set β) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ b, w = t1 b ∧ b ∈ Y}

end DomainTheory.NeighbourhoodSystems

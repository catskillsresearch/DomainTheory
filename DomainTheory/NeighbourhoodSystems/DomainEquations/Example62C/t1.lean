module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-- Middle tag `1b = some (inr (inl b))`. -/
def t1 {α β γ : Type*} (b : β) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inl b))

end DomainTheory.NeighbourhoodSystems

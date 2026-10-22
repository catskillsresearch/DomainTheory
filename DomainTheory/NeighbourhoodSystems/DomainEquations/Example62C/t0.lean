module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-- Left tag `0a = some (inl a)`. -/
def t0 {α β γ : Type*} (a : α) : Option (α ⊕ β ⊕ γ) := some (Sum.inl a)

end DomainTheory.NeighbourhoodSystems

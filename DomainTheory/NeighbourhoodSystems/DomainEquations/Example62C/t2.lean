module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-- Right tag `2c = some (inr (inr c))`. -/
def t2 {α β γ : Type*} (c : γ) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inr c))

end DomainTheory.NeighbourhoodSystems

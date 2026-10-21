/-ai
The function-space retract from a to b is the graph of the map sending u to the composition of b after u after a. Scott's formula (4.8) is a ∘→ b = λu. b ∘ u ∘ a.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.8).** Function space of retracts `a ∘→ b = λu. b ∘ u ∘ a`. -/
def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))

end DomainTheory.DataTypesAsLattices

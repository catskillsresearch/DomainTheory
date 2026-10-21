/-ai
The greatest postfixed point, below an element b, of the map sending z to the intersection of the image of z with b is the union of all sets contained in that intersection.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Greatest postfixed point of `z ↦ f z ∩ b` (Knaster–Tarski inf below `b`). -/
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}

end DomainTheory.DataTypesAsLattices

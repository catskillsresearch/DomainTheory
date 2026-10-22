module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Greatest postfixed point of `z ↦ f z ∩ b` (Knaster–Tarski inf below `b`). -/
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}

end DomainTheory.DataTypesAsLattices

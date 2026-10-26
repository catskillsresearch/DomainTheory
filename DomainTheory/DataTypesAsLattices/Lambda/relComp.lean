module

public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.3).** Relational composition. -/
def relComp (x y : Pomega) : Pomega :=
  {p | ∃ n m l, p = pair n l ∧ pair n m ∈ x ∧ pair m l ∈ y}

end DomainTheory.DataTypesAsLattices

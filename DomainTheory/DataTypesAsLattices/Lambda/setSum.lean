module

public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.4).** Set-sum. -/
def setSum (x y : Pomega) : Pomega :=
  {k | ∃ n m, n ∈ x ∧ m ∈ y ∧ k = n + m}

end DomainTheory.DataTypesAsLattices

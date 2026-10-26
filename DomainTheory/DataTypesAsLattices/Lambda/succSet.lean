module

public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** Successor `x + 1 = {n + 1 | n ∈ x}`. -/
def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}

end DomainTheory.DataTypesAsLattices

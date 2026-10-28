module

public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}

end DomainTheory.DataTypesAsLattices

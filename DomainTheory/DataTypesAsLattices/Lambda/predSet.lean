module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}

end DomainTheory.DataTypesAsLattices

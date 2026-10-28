module

public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}

end DomainTheory.DataTypesAsLattices

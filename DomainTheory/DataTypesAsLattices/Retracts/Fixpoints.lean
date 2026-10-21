/-ai
The fixed-point set of an endomap of Pω is the set of elements that the map sends to themselves.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The range / fixed-point set of a map. -/
def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}

end DomainTheory.DataTypesAsLattices

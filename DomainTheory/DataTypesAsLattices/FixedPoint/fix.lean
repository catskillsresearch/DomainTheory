module

public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

end DomainTheory.DataTypesAsLattices

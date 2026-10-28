module

public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

end DomainTheory.DataTypesAsLattices

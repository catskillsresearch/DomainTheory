module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Tag and payload of a seven-sum abstract-syntax code. -/
def expTag (e : Pomega) : Pomega := funOf e (ofNat 0)

end DomainTheory.DataTypesAsLattices

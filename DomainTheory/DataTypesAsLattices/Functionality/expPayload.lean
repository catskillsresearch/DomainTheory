module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def expPayload (e : Pomega) : Pomega := funOf e (ofNat 1)

end DomainTheory.DataTypesAsLattices

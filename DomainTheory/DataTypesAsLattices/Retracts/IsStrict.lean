module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def IsStrict (a : Pomega) : Prop :=
  funOf a botElem = botElem

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def typed (u a : Pomega) : Prop :=
  u = funOf a u

end DomainTheory.DataTypesAsLattices

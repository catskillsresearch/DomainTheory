module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

class Retract (a : Pomega) : Prop where
  out : a = comp a a

end DomainTheory.DataTypesAsLattices

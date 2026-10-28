
module

public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def RestrictedEquiv.mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

end DomainTheory.DataTypesAsLattices


module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.diagC
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def pairMed (f g c : Pomega) : Pomega :=
  comp (tensorR f g) (comp diagC c)

end DomainTheory.DataTypesAsLattices

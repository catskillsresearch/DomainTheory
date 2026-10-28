
module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.diagC
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def pairMed (f g c : Pomega) : Pomega :=
  comp (tensorR f g) (comp diagC c)

end DomainTheory.DataTypesAsLattices

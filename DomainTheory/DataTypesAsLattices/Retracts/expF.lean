module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.tensor4
public import DomainTheory.DataTypesAsLattices.Retracts.plus7

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def expF (z : Pomega) : Pomega :=
  plus7 intR botElem z z (tensor4 z z z z) (tensorR z z) (tensorR intR z)

end DomainTheory.DataTypesAsLattices

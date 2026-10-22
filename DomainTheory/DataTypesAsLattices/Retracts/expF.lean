module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.tensor4
public import DomainTheory.DataTypesAsLattices.Retracts.plus7

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.44).** Abstract-syntax functor. -/
def expF (z : Pomega) : Pomega :=
  plus7 intR botElem z z (tensor4 z z z z) (tensorR z z) (tensorR intR z)

end DomainTheory.DataTypesAsLattices

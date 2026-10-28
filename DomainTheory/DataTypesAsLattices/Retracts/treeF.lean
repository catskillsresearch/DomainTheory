module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.intR

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lambF (z : Pomega) : Pomega := plusR intR (arrowR z z)

end DomainTheory.DataTypesAsLattices

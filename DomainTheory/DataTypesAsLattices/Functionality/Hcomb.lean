module

public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.envR
public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.45).** `ℋ : exp → (env → lamb)`, the retract of the
least fixed point of the syntax-directed continuous operator. -/
def Hcomb : Pomega :=
  funOf (arrowR expR (arrowR envR lambR)) Hfun

end DomainTheory.DataTypesAsLattices

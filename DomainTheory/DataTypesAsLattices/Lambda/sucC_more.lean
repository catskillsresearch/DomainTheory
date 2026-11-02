module

public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace sucC

theorem app (x : Pomega) : funOf sucC x = succSet x :=
  beta succSet.isScottContinuous x

end sucC

end DomainTheory.DataTypesAsLattices

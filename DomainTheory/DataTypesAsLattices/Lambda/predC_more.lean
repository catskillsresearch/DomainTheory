module

public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace predC

theorem app (x : Pomega) : funOf predC x = predSet x :=
  beta predSet.isScottContinuous x

end predC

end DomainTheory.DataTypesAsLattices

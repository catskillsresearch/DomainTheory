module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem predC_app (x : Pomega) : funOf predC x = predSet x :=
  beta predSet_isScottContinuous x

end DomainTheory.DataTypesAsLattices

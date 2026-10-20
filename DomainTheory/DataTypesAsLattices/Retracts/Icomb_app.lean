module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem Icomb_app (x : Pomega) : funOf Icomb x = x :=
  beta id_isScottContinuous x

end DomainTheory.DataTypesAsLattices

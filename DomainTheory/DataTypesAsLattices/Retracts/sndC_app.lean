module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











theorem sndC_app (u : Pomega) : funOf sndC u = funOf u (ofNat 1) :=
  beta (funOf_isScottContinuous_left (ofNat 1)) u

end DomainTheory.DataTypesAsLattices

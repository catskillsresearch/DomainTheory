module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











theorem fstC_app (u : Pomega) : funOf fstC u = funOf u (ofNat 0) :=
  beta (funOf_isScottContinuous_left (ofNat 0)) u

end DomainTheory.DataTypesAsLattices

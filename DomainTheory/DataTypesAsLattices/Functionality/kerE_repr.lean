module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices












theorem kerE_repr {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    (kerE a).rel x (funOf a x) :=
  (retract_app ha x).symm

end DomainTheory.DataTypesAsLattices

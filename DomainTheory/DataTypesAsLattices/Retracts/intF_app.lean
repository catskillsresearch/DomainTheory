module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intF_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intF_app (f u : Pomega) :
    funOf (intF f) u =
      dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u) :=
  beta (intF_map_isScottContinuous f) u

end DomainTheory.DataTypesAsLattices

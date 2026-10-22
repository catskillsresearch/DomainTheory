
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_body_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sumMed_app (f g u : Pomega) :
    funOf (sumMed f g) u =
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1))) :=
  beta (sumMed_body_isScottContinuous f g) u

end DomainTheory.DataTypesAsLattices

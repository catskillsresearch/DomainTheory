
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.outleftC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem outleftC_app (u : Pomega) :
    funOf outleftC u = condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem :=
  beta outleftC_isScottContinuous u

end DomainTheory.DataTypesAsLattices

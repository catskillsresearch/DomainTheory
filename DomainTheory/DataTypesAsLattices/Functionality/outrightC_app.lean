
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem outrightC_app (u : Pomega) :
    funOf outrightC u = condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)) :=
  beta outrightC_isScottContinuous u

end DomainTheory.DataTypesAsLattices

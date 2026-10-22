
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def hPred (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (expPayload e) t))
    (funOf inleftC (predSet (funOf outC (hApply H (expPayload e) t))))
    botElem

end DomainTheory.DataTypesAsLattices

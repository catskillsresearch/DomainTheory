/-ai
The successor clause sends H, an expression e, and an environment t to the conditional set of the tag of the value of H at the payload of e. The zero branch is the left injection of the successor of the untagged payload of that value, and the positive branch is bottom.
ai-/

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

def hSucc (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (expPayload e) t))
    (funOf inleftC (succSet (funOf outC (hApply H (expPayload e) t))))
    botElem

end DomainTheory.DataTypesAsLattices

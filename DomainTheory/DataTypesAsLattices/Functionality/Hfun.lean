/-ai
The raw least fixed point of the operator in (4.43) is the least fixed point of the continuous operator HF.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.HF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Raw least fixed point of the (4.43) operator. -/
def Hfun : Pomega := fix HF

end DomainTheory.DataTypesAsLattices

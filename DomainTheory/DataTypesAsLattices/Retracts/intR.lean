/-ai
The integer retract is the least fixed point of the integer functional, as in Scott's clause (4.7).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.intF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.7).** Integer retract as the least fixed point. -/
def intR : Pomega := fix intF

end DomainTheory.DataTypesAsLattices

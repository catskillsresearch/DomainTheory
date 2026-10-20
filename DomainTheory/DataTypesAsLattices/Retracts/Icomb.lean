module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- The identity combinator `I = λu. u`, the largest retract. -/
def Icomb : Pomega := graph (fun x => x)

end DomainTheory.DataTypesAsLattices

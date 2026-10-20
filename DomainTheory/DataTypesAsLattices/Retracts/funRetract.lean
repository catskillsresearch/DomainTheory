module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.1).** The function-space retract `fun = λu λx. u(x)`. -/
def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))

end DomainTheory.DataTypesAsLattices

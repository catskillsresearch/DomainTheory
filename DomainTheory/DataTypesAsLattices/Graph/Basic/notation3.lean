module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

infixl:70 " ⬝ " => funOf

end DomainTheory.DataTypesAsLattices

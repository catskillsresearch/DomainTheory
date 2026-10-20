module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- `x : A` means `x A x`. -/
def RestrictedEquiv.mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

end DomainTheory.DataTypesAsLattices

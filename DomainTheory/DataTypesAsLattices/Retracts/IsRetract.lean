module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §4, Definition.** `a` is a retract iff `a = a ∘ a`. -/
def IsRetract (a : Pomega) : Prop :=
  a = comp a a

end DomainTheory.DataTypesAsLattices

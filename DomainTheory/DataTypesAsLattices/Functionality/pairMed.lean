module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 4.4.** The product mediator
`h = (f ⊗ g) ∘ diag ∘ c`. -/
def pairMed (f g c : Pomega) : Pomega :=
  comp (tensorR f g) (comp diagC c)

end DomainTheory.DataTypesAsLattices

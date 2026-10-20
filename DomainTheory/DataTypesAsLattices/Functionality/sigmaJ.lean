module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (7.17).** Independent successor functions. -/
def sigmaJ (j : ℕ) (x : Pomega) : Pomega :=
  {p | ∃ k, pair j (k + 1) = p ∧ pair j k ∈ x}

end DomainTheory.DataTypesAsLattices

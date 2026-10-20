module

public import DomainTheory.DataTypesAsLattices.Continuous

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1, Definition / Table 2.**
`fun(u)(x) = {m | ∃ e n ⊆ x. (n, m) ∈ u}`. -/
def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}

end DomainTheory.DataTypesAsLattices

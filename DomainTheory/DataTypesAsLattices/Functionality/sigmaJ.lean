/-ai
Scott 1976, (7.17). The independent successor σ_j sends a set x to the set of codes of pairs (j, k + 1) for which the code of the pair (j, k) lies in x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (7.17).** Independent successor functions. -/
def sigmaJ (j : ℕ) (x : Pomega) : Pomega :=
  {p | ∃ k, pair j (k + 1) = p ∧ pair j k ∈ x}

end DomainTheory.DataTypesAsLattices

/-ai
Scott 1976, (2.4). The set-sum of x and y is the set of all sums n + m with n in x and m in y.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.4).** Set-sum. -/
def setSum (x y : Pomega) : Pomega :=
  {k | ∃ n m, n ∈ x ∧ m ∈ y ∧ k = n + m}

end DomainTheory.DataTypesAsLattices

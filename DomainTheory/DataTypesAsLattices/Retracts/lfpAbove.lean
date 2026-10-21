/-ai
The least upper bound of the iterates of f above a set x is the union over n of the n-fold iterate of f starting at x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Least upper bound of fixed points above `x`: `⋃_n fⁿ(x)`. -/
def lfpAbove (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, iterateFrom f x n

end DomainTheory.DataTypesAsLattices

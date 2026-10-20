module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Combinatory primitive-recursion step `λa λf λu λn. n ⊃ a, f(n−1)(u(n−1))`. -/
def primRecStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2 (.lam 3
    (.cond (.var 3) (.var 0)
      (.app (.app (.var 1) (.pred (.var 3)))
        (.app (.var 2) (.pred (.var 3))))))))

end DomainTheory.DataTypesAsLattices

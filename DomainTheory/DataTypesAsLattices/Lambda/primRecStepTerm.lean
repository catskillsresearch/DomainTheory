/-ai
The combinatory primitive-recursion step is the term that abstracts a base, a step, a functional, and an argument, and returns the conditional of the argument with the base in the zero branch and the step applied to the predecessor and then to the functional at the predecessor in the other branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Combinatory primitive-recursion step `λa λf λu λn. n ⊃ a, f(n−1)(u(n−1))`. -/
def primRecStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2 (.lam 3
    (.cond (.var 3) (.var 0)
      (.app (.app (.var 1) (.pred (.var 3)))
        (.app (.var 2) (.pred (.var 3))))))))

end DomainTheory.DataTypesAsLattices

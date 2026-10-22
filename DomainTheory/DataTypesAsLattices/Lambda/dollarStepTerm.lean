module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Paper combinator for `$`: `λs λu λz. z ⊃ u(0), s(λt. u(t+1))(z−1)`. -/
def dollarStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 2)
      (.app (.var 1) .zero)
      (.app (.app (.var 0) (.lam 3 (.app (.var 1) (.succ (.var 3)))))
        (.pred (.var 2))))))

end DomainTheory.DataTypesAsLattices

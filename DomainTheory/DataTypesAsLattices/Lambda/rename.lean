module

public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def rename (i j : ℕ) : Term → Term
  | .var k => if k = i then .var j else .var k
  | .zero => .zero
  | .succ t => .succ (rename i j t)
  | .pred t => .pred (rename i j t)
  | .cond z x y => .cond (rename i j z) (rename i j x) (rename i j y)
  | .app u x => .app (rename i j u) (rename i j x)
  | .lam k body => if k = i then .lam k body else .lam k (rename i j body)

end DomainTheory.DataTypesAsLattices

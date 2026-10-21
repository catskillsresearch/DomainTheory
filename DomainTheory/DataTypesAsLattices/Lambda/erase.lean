/-ai
Erasure sends a λ-term to a combinator. Variables and zero stay as they are, successor and predecessor become applications of the corresponding combinators, a conditional becomes the conditional combinator applied to the erased left branch, then the erased right branch, then the erased test, application is preserved, and abstraction becomes combinatory abstraction at the bound index.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.abs

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def erase : Term → Comb
  | .var i => .var i
  | .zero => .zero
  | .succ t => .app .suc (erase t)
  | .pred t => .app .pred (erase t)
  | .cond z x y => .app (.app (.app .cond (erase x)) (erase y)) (erase z)
  | .app u x => .app (erase u) (erase x)
  | .lam i body => abs i (erase body)

end DomainTheory.DataTypesAsLattices

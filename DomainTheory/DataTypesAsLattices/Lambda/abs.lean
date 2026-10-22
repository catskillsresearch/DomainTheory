
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def abs (i : ℕ) : Comb → Comb
  | .var j => if j = i then .app (.app .S .K) .K else .app .K (.var j)
  | .zero => .app .K .zero
  | .suc => .app .K .suc
  | .pred => .app .K .pred
  | .cond => .app .K .cond
  | .K => .app .K .K
  | .S => .app .K .S
  | .app u v => .app (.app .S (abs i u)) (abs i v)

end DomainTheory.DataTypesAsLattices


module

public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Lambda.Term

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- `i` occurs anywhere in `t` (free or bound). Freshness for (α). -/
def Occurs (i : ℕ) : Term → Prop
  | .var j => j = i
  | .zero => False
  | .succ t => Occurs i t
  | .pred t => Occurs i t
  | .cond z x y => Occurs i z ∨ Occurs i x ∨ Occurs i y
  | .app u x => Occurs i u ∨ Occurs i x
  | .lam k body => k = i ∨ Occurs i body

end DomainTheory.DataTypesAsLattices

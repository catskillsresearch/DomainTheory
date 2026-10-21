/-ai
A variable i occurs in a term, whether free or bound, as needed for freshness in the alpha law, when the term is the variable i, when it occurs in the argument of a successor or a predecessor, when it occurs in any immediate subterm of a conditional or an application, or when an abstraction binds i or it occurs in the body. The constant zero has no occurrence of i.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

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

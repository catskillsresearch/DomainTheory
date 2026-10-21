/-ai
The interpretation of a combinatory term in an environment reads a variable from the environment, sends zero, successor, predecessor, conditional, K, and S to the corresponding combinators, and interprets an application as application of the interpretations.
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

def ofComb : Comb → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => zeroC
  | .suc, _ => sucC
  | .pred, _ => predC
  | .cond, _ => condC
  | .K, _ => Kcomb
  | .S, _ => Scomb
  | .app u v, ρ => funOf (ofComb u ρ) (ofComb v ρ)

end DomainTheory.DataTypesAsLattices

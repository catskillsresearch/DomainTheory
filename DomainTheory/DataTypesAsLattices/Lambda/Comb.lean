/-ai
A combinatory expression is a variable, one of the six constants zero, successor, predecessor, conditional, K, and S, or an application of two combinatory expressions.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Combinatory expressions generated from the six constants and variables. -/
inductive Comb where
  | var : ℕ → Comb
  | zero | suc | pred | cond | K | S
  | app : Comb → Comb → Comb

end DomainTheory.DataTypesAsLattices

/-ai
Scott's Table 2 defines a LAMBDA term to be a variable, the constant zero, a successor, a predecessor, a conditional of three terms, an application of two terms, or an abstraction of a term in a variable.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** Syntax of LAMBDA. -/
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term

end DomainTheory.DataTypesAsLattices

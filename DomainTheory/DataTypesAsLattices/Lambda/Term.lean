
module

public import DomainTheory.DataTypesAsLattices.Graph.lam
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term

end DomainTheory.DataTypesAsLattices

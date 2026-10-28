module

public import DomainTheory.DataTypesAsLattices.Graph.lam

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

inductive LambTerm where
  | var : ℕ → LambTerm
  | zero : LambTerm
  | succ : LambTerm → LambTerm
  | pred : LambTerm → LambTerm
  | condq : LambTerm → LambTerm → LambTerm → LambTerm → LambTerm
  | app : LambTerm → LambTerm → LambTerm
  | lam : ℕ → LambTerm → LambTerm

end DomainTheory.DataTypesAsLattices

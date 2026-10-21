/-ai
Scott 1976, (4.43). A modified lambda term for the lambda model is a variable given by a natural number, the constant zero, the successor or predecessor of a term, a conditional with four subterms, an application of one term to another, or an abstraction binding a natural-number index in a term.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.43).** Modified LAMBDA terms for the `lamb` model. -/
inductive LambTerm where
  | var : ℕ → LambTerm
  | zero : LambTerm
  | succ : LambTerm → LambTerm
  | pred : LambTerm → LambTerm
  | condq : LambTerm → LambTerm → LambTerm → LambTerm → LambTerm
  | app : LambTerm → LambTerm → LambTerm
  | lam : ℕ → LambTerm → LambTerm

end DomainTheory.DataTypesAsLattices

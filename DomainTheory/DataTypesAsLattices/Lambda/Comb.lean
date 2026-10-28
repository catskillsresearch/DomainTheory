
module

public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

inductive Comb where
  | var : ℕ → Comb
  | zero | suc | pred | cond | K | S
  | app : Comb → Comb → Comb

end DomainTheory.DataTypesAsLattices

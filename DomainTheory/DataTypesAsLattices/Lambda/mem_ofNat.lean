/-ai
A number lies in the numeral n if and only if it equals n.

The equivalence is the definition of the numeral.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

@[simp] theorem mem_ofNat {n k : ℕ} : k ∈ ofNat n ↔ k = n := by simp [ofNat]

end DomainTheory.DataTypesAsLattices

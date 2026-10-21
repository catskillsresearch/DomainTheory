/-ai
Scott 1976, (2.1), defines the maximal extension of a sequence at a set, without a decidability side condition. A number lies in the extension when the set is empty and the number lies in every value of the sequence, or the set is the numeral n and the number lies in the value at n, or the set is neither empty nor any numeral.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.1).** Maximal extension, written without a decidability side condition. -/
def maxExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  {k | (x = ∅ ∧ ∀ n, k ∈ p n) ∨
    (∃ n, x = ofNat n ∧ k ∈ p n) ∨
    (x ≠ ∅ ∧ ∀ n, x ≠ ofNat n)}

end DomainTheory.DataTypesAsLattices

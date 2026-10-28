module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def maxExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  {k | (x = ∅ ∧ ∀ n, k ∈ p n) ∨
    (∃ n, x = ofNat n ∧ k ∈ p n) ∨
    (x ≠ ∅ ∧ ∀ n, x ≠ ofNat n)}

end DomainTheory.DataTypesAsLattices

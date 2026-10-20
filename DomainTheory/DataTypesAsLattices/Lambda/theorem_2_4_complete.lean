module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.erase_correct

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































/-- **Scott 1976, Theorem 2.4 (The combinator theorem).** Every LAMBDA
term equals an applicative combination of the six constants and its
free variables. -/
theorem theorem_2_4_complete (t : Term) (ρ : ℕ → Pomega) :
    interp t ρ = ofComb (erase t) ρ :=
  (erase_correct t ρ).symm

end DomainTheory.DataTypesAsLattices

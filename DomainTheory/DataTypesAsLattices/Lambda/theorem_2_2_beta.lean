module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_1

@[expose] public section


namespace DomainTheory.DataTypesAsLattices












/-- **Scott 1976, Theorem 2.2 (β).** -/
theorem theorem_2_2_beta (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  beta (theorem_2_1 body ρ i) y

end DomainTheory.DataTypesAsLattices

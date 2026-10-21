/-ai
Scott 1976, Theorem 2.2 (β). Applying the interpretation of an abstraction to y equals the interpretation of the body in the environment updated by y at the bound variable.

This is the β-law, using the continuity theorem for the body in that variable.
ai-/
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

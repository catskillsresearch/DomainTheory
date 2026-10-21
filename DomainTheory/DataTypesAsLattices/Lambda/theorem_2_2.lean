/-ai
Scott 1976, Theorem 2.2 (The conversion theorem). The principles (α), (β), and (ξ) are valid in the model. Renaming a bound variable preserves the interpretation of an abstraction when the bodies agree after the rename. Applying an abstraction to y interprets the body in the environment updated at that variable. If two bodies agree at every value of the bound variable, their abstractions have the same interpretation.

The three conjuncts are the α, β, and ξ clauses of the conversion theorem.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_beta
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_xi
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2_alpha

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 2.2 (The conversion theorem).**
The three basic principles (α), (β), (ξ) are valid in the model. -/
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    (∀ j, (∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) →
        interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ) ∧
      funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) ∧
        ∀ σ, (∀ v, interp body (envSet ρ i v) = interp σ (envSet ρ i v)) →
          interp (.lam i body) ρ = interp (.lam i σ) ρ :=
  ⟨fun j h => theorem_2_2_alpha i j body ρ h,
    theorem_2_2_beta i body ρ y,
    fun _σ h => theorem_2_2_xi h⟩

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.rename

public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_1

@[expose] public section

namespace DomainTheory.DataTypesAsLattices
/-- **Scott 1976, Table 1 (α).** Bound variables may be renamed when the
bodies agree after the rename (Scott: "`x` is a bound variable"). -/
theorem theorem_2_2.alpha (i j : ℕ) (body : Term) (ρ : ℕ → Pomega)
    (h : ∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) :
    interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ := by
  unfold interp
  exact congrArg graph (funext h)

/-- **Scott 1976, Theorem 2.2 (ξ).** -/
theorem theorem_2_2.xi {i : ℕ} {τ σ : Term} {ρ : ℕ → Pomega}
    (h : ∀ v, interp τ (envSet ρ i v) = interp σ (envSet ρ i v)) :
    interp (.lam i τ) ρ = interp (.lam i σ) ρ := by
  simp [interp, h]

/-- **Scott 1976, Theorem 2.2 (β).** -/
theorem theorem_2_2.beta (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  DomainTheory.DataTypesAsLattices.beta (theorem_2_1 body ρ i) y

/-- **Scott 1976, Theorem 2.2 (The conversion theorem).**
The three basic principles (α), (β), (ξ) are valid in the model. -/
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    (∀ j, (∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) →
        interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ) ∧
      funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) ∧
        ∀ σ, (∀ v, interp body (envSet ρ i v) = interp σ (envSet ρ i v)) →
          interp (.lam i body) ρ = interp (.lam i σ) ρ :=
  ⟨fun j h => theorem_2_2.alpha i j body ρ h,
    theorem_2_2.beta i body ρ y,
    fun _σ h => theorem_2_2.xi h⟩

end DomainTheory.DataTypesAsLattices

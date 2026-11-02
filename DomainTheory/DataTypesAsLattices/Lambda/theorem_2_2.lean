module

public import DomainTheory.DataTypesAsLattices.Graph.beta

public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_1

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_2_2

theorem alpha (i j : ℕ) (body : Term) (ρ : ℕ → Pomega)
    (h : ∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) :
    interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ := by
  unfold interp
  exact congrArg graph (funext h)

theorem xi {i : ℕ} {τ σ : Term} {ρ : ℕ → Pomega}
    (h : ∀ v, interp τ (envSet ρ i v) = interp σ (envSet ρ i v)) :
    interp (.lam i τ) ρ = interp (.lam i σ) ρ := by
  simp [interp, h]

theorem beta (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) :=
  DomainTheory.DataTypesAsLattices.beta (theorem_2_1 body ρ i) y

end theorem_2_2

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

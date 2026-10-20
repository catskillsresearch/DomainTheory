module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices












/-- **Scott 1976, Theorem 2.2 (ξ).** -/
theorem theorem_2_2_xi {i : ℕ} {τ σ : Term} {ρ : ℕ → Pomega}
    (h : ∀ v, interp τ (envSet ρ i v) = interp σ (envSet ρ i v)) :
    interp (.lam i τ) ρ = interp (.lam i σ) ρ := by
  simp [interp, h]

end DomainTheory.DataTypesAsLattices

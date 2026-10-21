/-ai
Scott 1976, Theorem 2.2 (ξ). If two terms have the same interpretation at every value of a variable, then the abstractions of those terms at that variable have the same interpretation.

Simplification of the interpretation of an abstraction uses the assumed agreement of the bodies.
ai-/
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

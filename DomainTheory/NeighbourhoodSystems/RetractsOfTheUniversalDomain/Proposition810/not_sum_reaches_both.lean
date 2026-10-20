module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- No element of `𝒟₀+𝒟₁` reaches into both the left and the right copy (Exercise 3.18's
disjointness `inj₀_inter_inj₁`, plus `not_sum_mem_empty`). -/
theorem not_sum_reaches_both {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
    {w : (sum V₀ V₁ h₀ h₁).Element} (hL : ∃ X, V₀.mem X ∧ w.mem (inj₀ X))
    (hR : ∃ Y, V₁.mem Y ∧ w.mem (inj₁ Y)) : False := by
  obtain ⟨X, _, hX⟩ := hL
  obtain ⟨Y, _, hY⟩ := hR
  have h := w.inter_mem hX hY
  rw [inj₀_inter_inj₁] at h
  exact not_sum_mem_empty (w.sub h)

end DomainTheory.NeighbourhoodSystems

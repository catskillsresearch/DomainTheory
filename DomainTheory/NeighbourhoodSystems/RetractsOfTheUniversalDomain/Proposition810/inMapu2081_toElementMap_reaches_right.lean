module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- The image of `in₁` always reaches the right copy. -/
theorem inMap₁_toElementMap_reaches_right {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₁.Element) :
    ∃ Y, V₁.mem Y ∧ ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₁ Y) := by
  refine ⟨V₁.master, V₁.master_mem, V₁.master, v.master_mem, V₁.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inr ⟨V₁.master, V₁.master_mem, rfl⟩)

end DomainTheory.NeighbourhoodSystems

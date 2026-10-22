module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.19 (recovery of the relation).** `X, Y f Z ↔ Z ∈ f(↑X, ↑Y)`, the two-variable
analogue of Proposition 2.2(ii). -/
theorem rel₂_iff_mem_principal (f : ApproximableMap₂ V₀ V₁ V₂) {X : Set α} (hX : V₀.mem X)
    {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    f.rel X Y Z ↔ (f.toElementMap₂ (V₀.principal hX) (V₁.principal hY)).mem Z := by
  constructor
  · intro hrel
    exact ⟨X, Y, ⟨hX, subset_rfl⟩, ⟨hY, subset_rfl⟩, hrel⟩
  · rintro ⟨X', Y', ⟨_, hXX'⟩, ⟨_, hYY'⟩, hrel⟩
    exact f.mono hrel hXX' hYY' subset_rfl hX hY (f.rel_cod hrel)

end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems

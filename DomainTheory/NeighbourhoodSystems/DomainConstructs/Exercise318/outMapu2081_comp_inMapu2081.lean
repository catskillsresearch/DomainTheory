module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


















variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)


variable {V₀ V₁}
























variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}







/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₁ ∘ in₁ = I_{𝒟₁}`. -/
theorem outMap₁_comp_inMap₁ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₁ = idMap V₁ := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, hZ, ?_⟩
    have hYW : Y ⊆ rightPart V₁ W := by
      intro b hb
      rw [mem_rightPart]; exact Or.inl (hinj (ir_mem_inj₁.mpr hb))
    exact hYW.trans hsub
  · rintro ⟨hY, hZ, hYZ⟩
    refine ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), hZ, ?_⟩
    rw [rightPart_inj₁]; exact hYZ

end DomainTheory.NeighbourhoodSystems

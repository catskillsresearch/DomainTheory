/-ai
The composite of the left projection after the left injection is the identity map of the first neighbourhood system.

Two approximable maps agree when they relate the same pairs. If the composite relates X to Z, some sum neighbourhood receives the left copy of X and has left content contained in Z, so X is contained in that left content and hence in Z. Conversely, if X is contained in Z, the left copy of X is a sum neighbourhood related to X by the injection and to Z by the projection, because the left content of that copy is X.
ai-/
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







/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₀ ∘ in₀ = I_{𝒟₀}`. -/
theorem outMap₀_comp_inMap₀ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₀ = idMap V₀ := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, hZ, ?_⟩
    have hXW : X ⊆ leftPart V₀ W := by
      intro a ha
      rw [mem_leftPart]; exact Or.inl (hinj (il_mem_inj₀.mpr ha))
    exact hXW.trans hsub
  · rintro ⟨hX, hZ, hXZ⟩
    refine ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), hZ, ?_⟩
    rw [leftPart_inj₀]; exact hXZ

end DomainTheory.NeighbourhoodSystems

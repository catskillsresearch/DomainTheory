module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.mem_prodNbhd_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inl_preimage_prodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.inr_preimage_prodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- Scott's (1): inclusion of product nbhds is componentwise (uses disjointness of `Δ₀`, `Δ₁`). -/
theorem prodNbhd_subset_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y ⊆ prodNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have : (Sum.inl a : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using ha)
      simpa using this
    · have : (Sum.inr b : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using hb)
      simpa using this
  · rintro ⟨hX, hY⟩ (a | b) hs
    · simp only [mem_prodNbhd_inl] at hs ⊢; exact hX hs
    · simp only [mem_prodNbhd_inr] at hs ⊢; exact hY hs

end DomainTheory.NeighbourhoodSystems

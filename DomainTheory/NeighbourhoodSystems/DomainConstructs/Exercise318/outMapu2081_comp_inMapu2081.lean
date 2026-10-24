module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inMap₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inMap₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.outMap₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.outMap₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_inter_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_subset_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_subset_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁_subset_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster_inter_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sumMaster_inter_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_injective
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_preimage_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_preimage_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_mem

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

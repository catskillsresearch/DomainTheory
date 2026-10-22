module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **`out₁ ∘ in₀ = const ⊥`.** A left-injected element carries no right-hand information. -/
theorem outMap₁_comp_inMap₀ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁)) = constMap V₀ V₁.bot := by
  apply ApproximableMap.ext
  intro X Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hX, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, ?_⟩
    obtain ⟨a, ha⟩ := h₀ X hX
    have hmaster : rightPart V₁ (inj₀ X) ⊆ rightPart V₁ W := rightPart_mono V₁ hinj
    rw [rightPart_inj₀ V₁ ⟨a, ha⟩] at hmaster
    exact Set.Subset.antisymm (V₁.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hX, rfl⟩
    exact ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), V₁.master_mem, (rightPart_inj₀ V₁ (h₀ X hX)).subset⟩

end SumHelpers
end DomainTheory.NeighbourhoodSystems

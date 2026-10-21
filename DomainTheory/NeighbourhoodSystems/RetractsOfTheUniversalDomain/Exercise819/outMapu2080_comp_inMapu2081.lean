/-ai
The left projection after the right injection is the constant map whose value is the bottom element of the left summand.

Compare the relations. In one direction a witness contains the right injection of the input neighbourhood, so the left part of that injection is contained in the left part of the witness and hence in the output neighbourhood. The left part of a right injection is the master, so the output neighbourhood equals the master, and the input is a neighbourhood. In the other direction the right injection of the input itself is the witness, by the right-injection clause of sum membership and the same computation of its left part.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **`out₀ ∘ in₁ = const ⊥`.** A right-injected element carries no left-hand information. -/
theorem outMap₀_comp_inMap₁ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁)) = constMap V₁ V₀.bot := by
  apply ApproximableMap.ext
  intro Y Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hY, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, ?_⟩
    obtain ⟨b, hb⟩ := h₁ Y hY
    have hmaster : leftPart V₀ (inj₁ Y) ⊆ leftPart V₀ W := leftPart_mono V₀ hinj
    rw [leftPart_inj₁ V₀ ⟨b, hb⟩] at hmaster
    exact Set.Subset.antisymm (V₀.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hY, rfl⟩
    exact ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), V₀.master_mem, (leftPart_inj₁ V₀ (h₁ Y hY)).subset⟩

end SumHelpers
end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_bot_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `out₀(⊥) ≤ ⊥`: the basepoint carries no left-hand information. -/
theorem outMap₀_bot_le :
    (outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₀.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₀.sub_master hg.2.1) ?_
  have h2 : leftPart V₀ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [leftPart_sumMaster] at h2

end SumHelpers
end DomainTheory.NeighbourhoodSystems

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


section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `out₁(⊥) ≤ ⊥`: the basepoint carries no right-hand information. -/
theorem outMap₁_bot_le :
    (outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₁.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₁.sub_master hg.2.1) ?_
  have h2 : rightPart V₁ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [rightPart_sumMaster] at h2

end SumHelpers
end DomainTheory.NeighbourhoodSystems

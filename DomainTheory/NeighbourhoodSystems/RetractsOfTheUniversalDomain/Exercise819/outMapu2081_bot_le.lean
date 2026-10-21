/-ai
The right projection of the bottom element of a sum lies below the bottom element of the right summand.

The general inequality for the image of a bottom element reduces the claim to a neighbourhood of that image. One inclusion is the containment of that neighbourhood in the master. The other is the containment of the right part of the sum master in the neighbourhood, rewritten as the master of the right summand.
ai-/
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

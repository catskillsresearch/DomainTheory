module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_bot_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.TD_bot_eq_botElt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(⊥) ≤ ⊥`: the basepoint carries no tag information. Only the third `whichGuard` disjunct
applies at `W = (sum V₀ V₁ h₀ h₁).master`, forcing the output to `master`. -/
theorem which_bot_le :
    (whichMap V₀ V₁ h₀ h₁).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ Example23.botElt := by
  rw [← TD_bot_eq_botElt]
  refine toElementMap_bot_le _ ?_
  intro Y hg
  exact whichGuard_masterC hg.2.2 rfl

end SumHelpers
end DomainTheory.NeighbourhoodSystems

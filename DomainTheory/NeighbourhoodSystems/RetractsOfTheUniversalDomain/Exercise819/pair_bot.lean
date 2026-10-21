/-ai
The pairing of two bottom elements is the bottom element of the product.

The two inequalities are proved separately. A product neighbourhood in the pairing of the bottoms has both factors equal to the master neighbourhood, so it is the master of the product. The other inequality is the general fact that bottom lies below every element.
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


section General

variable {α β γ δ : Type*}

/-- The pairing of two bottoms is the bottom of the product. -/
theorem pair_bot {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β} :
    pair V0.bot V1.bot = (prod V0 V1).bot := by
  apply le_antisymm
  · intro W hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    rw [mem_bot] at hX hY
    subst hX; subst hY
    rw [mem_bot]
    exact prod_master.symm
  · exact NeighborhoodSystem.bot_le _ _

end General
end DomainTheory.NeighbourhoodSystems

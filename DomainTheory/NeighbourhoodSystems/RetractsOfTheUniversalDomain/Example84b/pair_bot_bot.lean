/-ai
The pair of the bottom of D and the bottom of E is the bottom of the product.

A product neighbourhood belongs to the pair of bottoms exactly when both factors belong to the bottoms, hence both are masters, and the neighbourhood is the product master. The product master is that same pair of masters, and both masters belong to the bottoms.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

/-- `(prod D E).bot = ⟨⊥_D, ⊥_E⟩`. -/
theorem pair_bot_bot : pair (D.bot) (E.bot) = (prod D E).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨D.master, E.master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

end Smash

end DomainTheory.NeighbourhoodSystems

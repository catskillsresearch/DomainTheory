/-ai
The first coordinate of the product bottom is the bottom of D.

Rewrite the product bottom as the pair of the two bottoms, and apply the first projection of a pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.pair_bot_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

@[simp] theorem prod_bot_fst : ((prod D E).bot).fst = D.bot := by rw [← pair_bot_bot, fst_pair]

end Smash

end DomainTheory.NeighbourhoodSystems

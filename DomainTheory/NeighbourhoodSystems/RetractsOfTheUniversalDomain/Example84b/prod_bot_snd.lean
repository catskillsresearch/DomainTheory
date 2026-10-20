module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.pair_bot_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Smash

@[simp] theorem prod_bot_snd : ((prod D E).bot).snd = E.bot := by rw [← pair_bot_bot, snd_pair]

end Smash

end DomainTheory.NeighbourhoodSystems

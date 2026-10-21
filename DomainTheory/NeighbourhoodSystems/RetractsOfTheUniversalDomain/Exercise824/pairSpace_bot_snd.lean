/-ai
The second component of the bottom of the pair space is the bottom of the function space.

Rewrite by the pairing of the two bottoms and by the second projection of a pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.pair_bot_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}










theorem pairSpace_bot_snd : ((PairSpace (E := E)).bot).snd = (funSpace E E).bot := by
  rw [← pair_bot_bot, snd_pair]

end Exercise824
end DomainTheory.NeighbourhoodSystems

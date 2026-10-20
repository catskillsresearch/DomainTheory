module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.pair_bot_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}










theorem pairSpace_bot_fst : ((PairSpace (E := E)).bot).fst = (funSpace E E).bot := by
  rw [← pair_bot_bot, fst_pair]

end Exercise824
end DomainTheory.NeighbourhoodSystems

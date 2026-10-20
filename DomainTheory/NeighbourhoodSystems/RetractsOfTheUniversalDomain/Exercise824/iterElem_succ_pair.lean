module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}











theorem iterElem_succ_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    (paired s t).iterElem (n + 1) = (paired s t).toElementMap ((paired s t).iterElem n) := by
  show ((paired s t).comp ((paired s t).iterMap n)).toElementMap (PairSpace (E := E)).bot
      = (paired s t).toElementMap (((paired s t).iterMap n).toElementMap (PairSpace (E := E)).bot)
  rw [toElementMap_comp]

end Exercise824
end DomainTheory.NeighbourhoodSystems

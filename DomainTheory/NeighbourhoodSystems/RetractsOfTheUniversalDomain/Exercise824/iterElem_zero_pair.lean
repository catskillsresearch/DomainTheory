module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.binOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}


theorem iterElem_zero_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    (paired s t).iterElem 0 = (PairSpace (E := E)).bot := by
  show (idMap (PairSpace (E := E))).toElementMap (PairSpace (E := E)).bot
      = (PairSpace (E := E)).bot
  rw [toElementMap_idMap]

end Exercise824
end DomainTheory.NeighbourhoodSystems

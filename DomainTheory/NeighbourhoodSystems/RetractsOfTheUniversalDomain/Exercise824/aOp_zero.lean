module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.binOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bStar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.aOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.bOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.pairSpace_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.iterElem_zero_pair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}


theorem aOp_zero (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    aOp s t 0 = constMap E E.bot := by
  show toApproxMap ((paired s t).iterElem 0).fst = constMap E E.bot
  rw [iterElem_zero_pair, pairSpace_bot_fst, Exercise823.toApproxMap_bot_eq_constMap]

end Exercise824
end DomainTheory.NeighbourhoodSystems

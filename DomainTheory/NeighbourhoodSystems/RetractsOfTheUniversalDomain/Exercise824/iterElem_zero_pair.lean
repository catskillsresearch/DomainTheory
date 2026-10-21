/-ai
The zeroth iterate element of the paired map is the bottom of the pair space.

Unfold the left side as the identity map of the pair space applied to that bottom, and rewrite by the element action of the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.Basic

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

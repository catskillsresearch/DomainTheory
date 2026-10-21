/-ai
The second component of the simultaneous fixed point is the map read from the second component of the fixed element of the operator that pairs the two given maps out of the pair space.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- Scott's `‖t‖ = fix(⟨s, t⟩)`'s second component, as an actual approximable map `E → E`. -/
def bStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap (paired s t).fixElement.snd

end Exercise824

end DomainTheory.NeighbourhoodSystems

/-ai
The first component of the simultaneous fixed point is the map read from the first component of the fixed element of the operator that pairs the two given maps out of the pair space.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- Scott's `‖s‖ = fix(⟨s, t⟩)`'s first component, as an actual approximable map `E → E`. -/
def aStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap (paired s t).fixElement.fst

end Exercise824

end DomainTheory.NeighbourhoodSystems

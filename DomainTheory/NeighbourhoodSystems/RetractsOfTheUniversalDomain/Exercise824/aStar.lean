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

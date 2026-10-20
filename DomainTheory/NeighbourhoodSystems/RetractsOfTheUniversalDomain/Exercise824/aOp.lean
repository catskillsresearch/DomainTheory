module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- The `n`-th approximant's first component, as an actual approximable map `E → E`. -/
def aOp (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    ApproximableMap E E :=
  toApproxMap ((paired s t).iterElem n).fst

end Exercise824

end DomainTheory.NeighbourhoodSystems

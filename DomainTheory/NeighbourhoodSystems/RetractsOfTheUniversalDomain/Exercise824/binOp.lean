module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.PairSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- Scott's `s(a, b)`: the operator `(E → E) × (E → E) → (E → E)` induced by an approximable map
`s` out of the pair space, applied to two actual maps `a b : E → E`. -/
def binOp (f : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (a b : ApproximableMap E E) : ApproximableMap E E :=
  toApproxMap (f.toElementMap (pair (toFilter a) (toFilter b)))

end Exercise824

end DomainTheory.NeighbourhoodSystems

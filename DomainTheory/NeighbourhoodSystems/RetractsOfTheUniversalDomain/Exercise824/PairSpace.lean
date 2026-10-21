/-ai
The pair space of a neighbourhood system is the product of its function space with itself. Its tokens are sums of two approximable self-maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-- Scott's pair space `(E → E) × (E → E)`: pairs of self-maps of `E`, as an actual
`NeighborhoodSystem` (Lecture III's product of two copies of the function space). -/
abbrev PairSpace : NeighborhoodSystem (ApproximableMap E E ⊕ ApproximableMap E E) :=
  prod (funSpace E E) (funSpace E E)

end Exercise824

end DomainTheory.NeighbourhoodSystems

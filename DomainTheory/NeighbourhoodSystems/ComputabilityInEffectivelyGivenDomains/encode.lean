module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.encodeListBool

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Tag-based Gödel code for an `SExpr` (tags `0..3` for the four constructors). -/
def SExpr.encode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (encode a) (encode b))
  | .cap a b => Nat.pair 3 (Nat.pair (encode a) (encode b))

end Exercise722

end DomainTheory.NeighbourhoodSystems

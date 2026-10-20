module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Subexpression depth (for fuelled decoding). -/
def sexprDepth : SExpr → ℕ
  | .sigma => 1
  | .single _ => 1
  | .cat a b => 1 + max (sexprDepth a) (sexprDepth b)
  | .cap a b => 1 + max (sexprDepth a) (sexprDepth b)

end Exercise722

end DomainTheory.NeighbourhoodSystems

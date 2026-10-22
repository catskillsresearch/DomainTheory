module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- The (finite) set of variables occurring in a formula. -/
def vars : Formula → Finset ℕ
  | .var i => {i}
  | .bot => ∅
  | .top => ∅
  | .neg φ => vars φ
  | .and φ ψ => vars φ ∪ vars ψ
  | .or φ ψ => vars φ ∪ vars ψ

end DomainTheory.NeighbourhoodSystems

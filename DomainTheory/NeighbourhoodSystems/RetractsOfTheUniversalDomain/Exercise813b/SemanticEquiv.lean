module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **Scott's Lindenbaum equivalence**: `φ ~ ψ` iff they agree under every truth valuation. -/
def SemanticEquiv (φ ψ : Formula) : Prop := ∀ v, evalV v φ = evalV v ψ

end DomainTheory.NeighbourhoodSystems

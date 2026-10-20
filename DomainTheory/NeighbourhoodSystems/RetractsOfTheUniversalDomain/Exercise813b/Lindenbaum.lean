module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **The Lindenbaum algebra of propositional calculus**: `Formula` quotiented by semantic
equivalence. -/
def Lindenbaum : Type := Quotient formulaSetoid

end DomainTheory.NeighbourhoodSystems

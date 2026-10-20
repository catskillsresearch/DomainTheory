module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.semanticEquiv_iff_evalSet_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- The canonical map to `Set ℕ`, well-defined by `semanticEquiv_iff_evalSet_eq`. -/
def Lindenbaum.toSet : Lindenbaum → Set ℕ :=
  Quotient.lift evalSet fun _ _ h => semanticEquiv_iff_evalSet_eq.mp h

end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.45).** `ℋ⟦τ⟧` as a map `env → lamb`. -/
def Htyped (τ : LambTerm) : Pomega :=
  funOf (arrowR envR lambR) (graph (Hinterp τ))

end DomainTheory.DataTypesAsLattices

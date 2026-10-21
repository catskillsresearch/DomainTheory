/-ai
Scott 1976, (4.45). The typed interpretation of a lambda term is the arrow retract from environments to lambda values applied to the graph of the interpretation of the term.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Hinterp

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.45).** `ℋ⟦τ⟧` as a map `env → lamb`. -/
def Htyped (τ : LambTerm) : Pomega :=
  funOf (arrowR envR lambR) (graph (Hinterp τ))

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Pairing of elements of `Pω` as a graph (Table 2 / (2.21)). -/
def pairElem (x y : Pomega) : Pomega := seq2 x y

end DomainTheory.DataTypesAsLattices

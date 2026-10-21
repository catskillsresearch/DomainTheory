/-ai
Scott 1976, (7.15) and (7.16). The iterator at stage zero returns its value argument. At the successor of a stage it applies the function argument to the iterator at the previous stage.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (7.15)–(7.16).** Iterators `Zₙ`. -/
def Z : ℕ → Pomega → Pomega → Pomega
  | 0, _, x => x
  | n + 1, f, x => funOf f (Z n f x)

end DomainTheory.DataTypesAsLattices

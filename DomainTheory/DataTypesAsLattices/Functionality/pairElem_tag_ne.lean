/-ai
The element pair of zero with x is distinct from the element pair of one with y.

This is the separation of those two tags for two-place sequences.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem pairElem_tag_ne (x y : Pomega) :
    pairElem (ofNat 0) x ≠ pairElem (ofNat 1) y :=
  seq2_tag_ne x y

end DomainTheory.DataTypesAsLattices

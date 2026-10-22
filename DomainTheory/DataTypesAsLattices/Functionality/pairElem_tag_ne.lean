
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem pairElem_tag_ne (x y : Pomega) :
    pairElem (ofNat 0) x ≠ pairElem (ofNat 1) y :=
  seq2_tag_ne x y

end DomainTheory.DataTypesAsLattices

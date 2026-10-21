/-ai
The application at the numeral 0 of the tag injection of x at i equals the numeral i.

This is the zeroth-component law for sequence pairs.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tagInj_zero (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 0) = ofNat i :=
  pairSeq_app_zero (ofNat i) x

end DomainTheory.DataTypesAsLattices

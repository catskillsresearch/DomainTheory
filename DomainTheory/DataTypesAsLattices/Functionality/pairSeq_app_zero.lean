/-ai
Application of a sequence pair at zero returns the left argument.

This is the zero-place application equation for the two-place sequence.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairSeq_app_zero (x y : Pomega) : funOf (pairSeq x y) (ofNat 0) = x :=
  seq2_app_zero x y

end DomainTheory.DataTypesAsLattices

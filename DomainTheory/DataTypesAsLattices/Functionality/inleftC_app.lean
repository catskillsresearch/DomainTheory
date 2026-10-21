/-ai
Application of the left injection to x is the sequence pair of zero with x.

This is β-conversion for the graph of sequence pairing in the right argument at the constant zero, which is Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem inleftC_app (x : Pomega) :
    funOf inleftC x = pairSeq (ofNat 0) x :=
  beta (pairSeq_isScottContinuous_right (ofNat 0)) x

end DomainTheory.DataTypesAsLattices

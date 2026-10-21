/-ai
Tag injection at a numeral i is Scott continuous.

It is right continuity of sequence pairing at the numeral i.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem tagInj_isScottContinuous (i : ℕ) :
    IsScottContinuous (tagInj i) :=
  pairSeq_isScottContinuous_right (ofNat i)

end DomainTheory.DataTypesAsLattices

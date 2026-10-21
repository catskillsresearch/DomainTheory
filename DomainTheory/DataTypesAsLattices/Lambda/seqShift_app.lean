/-ai
Applying the sequence shift of u to z equals the sequence revaluation of u at the successor of z.

This is the β-law for that body, which is Scott continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices








































theorem seqShift_app (u z : Pomega) :
    funOf (seqShift u) z = seqFun u (succSet z) :=
  beta (seqShift_isScottContinuous u) z

end DomainTheory.DataTypesAsLattices

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

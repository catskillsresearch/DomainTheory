module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_right_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices








































theorem seqShift_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun z => seqFun u (succSet z)) :=
  theorem_1_3 (seqFun_right_isScottContinuous u) succSet_isScottContinuous

end DomainTheory.DataTypesAsLattices

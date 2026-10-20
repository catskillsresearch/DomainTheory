module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices








































theorem seqShift_left_isScottContinuous : IsScottContinuous seqShift :=
  graph_const_isScottContinuous (fun u z => seqFun u (succSet z))
    (fun z => seqFun_left_isScottContinuous (succSet z))

end DomainTheory.DataTypesAsLattices

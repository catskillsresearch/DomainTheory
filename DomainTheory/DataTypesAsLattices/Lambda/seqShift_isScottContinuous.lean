/-ai
For each u, the map sending z to the sequence revaluation of u at the successor of z is Scott continuous.

This is the substitution theorem applied to the Scott continuity of the right-hand sequence map at u and the Scott continuity of the successor.
ai-/
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

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dollarStepBody_isScottContinuous_z (s u : Pomega) :
    IsScottContinuous (fun z => dollarStepBody s u z) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left (funOf u (ofNat 0)) y)
    (fun z => condSet_isScottContinuous_right z (funOf u (ofNat 0)))
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous (funOf s (seqShift u)))
      predSet_isScottContinuous)

end DomainTheory.DataTypesAsLattices

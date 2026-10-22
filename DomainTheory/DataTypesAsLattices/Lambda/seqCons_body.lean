module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seqCons_body (x xs : Pomega) :
    IsScottContinuous (fun z => condSet z x (funOf xs (predSet z))) :=
  theorem_1_3_tuple
    (fun _ => condSet_isScottContinuous_left x _)
    (fun z => condSet_isScottContinuous_right z x)
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous xs) predSet_isScottContinuous)

end DomainTheory.DataTypesAsLattices

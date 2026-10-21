/-ai
With the head and the tail fixed, the body of cons is Scott continuous.

The tuple form of Theorem 1.3 uses continuity of the conditional in its left and right arguments, continuity of the identity, and Theorem 1.3 applied to continuity of application at the tail composed with continuity of the predecessor.
ai-/
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

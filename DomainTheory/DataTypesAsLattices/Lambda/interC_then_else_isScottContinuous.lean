module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem interC_then_else_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y)))) :=
  theorem_1_3_tuple
    (fun els => condSet_isScottContinuous_mid x els)
    (fun th => condSet_isScottContinuous_right x th)
    (condSet_isScottContinuous_left (ofNat 0) botElem)
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous (funOf interC (predSet x)))
        predSet_isScottContinuous))

end DomainTheory.DataTypesAsLattices

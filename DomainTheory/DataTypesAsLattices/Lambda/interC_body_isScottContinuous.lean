module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.interC_else_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem interC_body_isScottContinuous :
    IsScottContinuous (fun x =>
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y))))) :=
  graph_const_isScottContinuous
    (fun x y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))))
    (fun y =>
      theorem_1_3_tuple
        (fun els => condSet_isScottContinuous_left
          (condSet y (ofNat 0) botElem) els)
        (fun tes => condSet_isScottContinuous_right tes
          (condSet y (ofNat 0) botElem))
        id_isScottContinuous
        (interC_else_isScottContinuous y))

end DomainTheory.DataTypesAsLattices

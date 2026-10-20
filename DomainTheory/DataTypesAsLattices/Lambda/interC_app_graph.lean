module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.interC_unfold
public import DomainTheory.DataTypesAsLattices.Lambda.interC_body_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem interC_app_graph (x : Pomega) :
    funOf interC x =
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y)))) := by
  nth_rw 1 [interC_unfold]
  exact beta interC_body_isScottContinuous x

end DomainTheory.DataTypesAsLattices

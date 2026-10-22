module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem primRecStep_isScottContinuous (a f : Pomega) :
    IsScottContinuous (primRecStep a f) :=
  graph_const_isScottContinuous
    (fun u n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))
    (fun n => theorem_1_3 (condSet_isScottContinuous_right n a)
      (theorem_1_3 (funOf_isScottContinuous (funOf f (predSet n)))
        (funOf_isScottContinuous_left (predSet n))))

end DomainTheory.DataTypesAsLattices

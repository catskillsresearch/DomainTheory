module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_inner_cont (u v : Pomega) :
    IsScottContinuous (fun x => funOf (funOf u x) (funOf v x)) :=
  theorem_1_3_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous u)
    (funOf_isScottContinuous v)

end DomainTheory.DataTypesAsLattices

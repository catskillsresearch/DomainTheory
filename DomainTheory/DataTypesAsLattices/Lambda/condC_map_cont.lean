module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem condC_map_cont :
    IsScottContinuous (fun x => graph (fun y => graph (fun z => condSet z x y))) :=
  graph_const_isScottContinuous
    (fun x y => graph (fun z => condSet z x y))
    (fun y => graph_const_isScottContinuous (fun x z => condSet z x y)
      (fun z => condSet_isScottContinuous_mid z y))

end DomainTheory.DataTypesAsLattices

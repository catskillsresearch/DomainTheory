
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_map_cont :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v => graph_const_isScottContinuous
      (fun u x => funOf (funOf u x) (funOf v x))
      (fun x => theorem_1_3
        (f := fun t => funOf t (funOf v x))
        (g := fun u => funOf u x)
        (funOf_isScottContinuous_left (funOf v x))
        (funOf_isScottContinuous_left x)))

end DomainTheory.DataTypesAsLattices

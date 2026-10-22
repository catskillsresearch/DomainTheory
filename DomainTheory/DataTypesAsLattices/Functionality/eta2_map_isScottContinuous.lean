module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eta2_map_isScottContinuous (f : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf (funOf f x) y)) :=
  graph_const_isScottContinuous
    (fun x y => funOf (funOf f x) y)
    (fun y =>
      theorem_1_3
        (f := fun t => funOf t y)
        (g := funOf f)
        (funOf_isScottContinuous_left y)
        (funOf_isScottContinuous f))

end DomainTheory.DataTypesAsLattices

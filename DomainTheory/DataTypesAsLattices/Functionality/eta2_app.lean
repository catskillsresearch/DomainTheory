module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eta2_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eta2_app (f x : Pomega) :
    funOf (graph (fun z => graph (fun y => funOf (funOf f z) y))) x =
      graph (fun y => funOf (funOf f x) y) :=
  beta (eta2_map_isScottContinuous f) x

end DomainTheory.DataTypesAsLattices

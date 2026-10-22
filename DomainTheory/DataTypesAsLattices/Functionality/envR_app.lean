module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.envR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem envR_app (t : Pomega) :
    funOf envR t = graph (fun n => funOf lambR (funOf t n)) :=
  beta envR_map_isScottContinuous t

end DomainTheory.DataTypesAsLattices

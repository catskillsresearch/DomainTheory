module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem envR_map_isScottContinuous :
    IsScottContinuous (fun t => graph (fun n => funOf lambR (funOf t n))) :=
  graph_const_isScottContinuous
    (fun t n => funOf lambR (funOf t n))
    (fun n => theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous_left n))

end DomainTheory.DataTypesAsLattices

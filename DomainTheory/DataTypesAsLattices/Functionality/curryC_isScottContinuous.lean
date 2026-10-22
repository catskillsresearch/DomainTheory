module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryC_isScottContinuous :
    IsScottContinuous (fun u =>
      graph (fun x => graph (fun y => funOf u (pairSeq x y)))) :=
  graph_const_isScottContinuous
    (fun u x => graph (fun y => funOf u (pairSeq x y)))
    (fun x =>
      graph_const_isScottContinuous
        (fun u y => funOf u (pairSeq x y))
        (fun y => funOf_isScottContinuous_left (pairSeq x y)))

end DomainTheory.DataTypesAsLattices

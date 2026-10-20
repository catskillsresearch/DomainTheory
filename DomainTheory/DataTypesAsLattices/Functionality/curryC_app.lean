module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem curryC_app (u : Pomega) :
    funOf curryC u = graph (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  beta curryC_isScottContinuous u

end DomainTheory.DataTypesAsLattices

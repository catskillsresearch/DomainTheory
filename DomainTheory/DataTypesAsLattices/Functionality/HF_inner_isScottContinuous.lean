module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem HF_inner_isScottContinuous (H : Pomega) :
    IsScottContinuous (fun e => graph (fun t => Hstep H e t)) :=
  graph_const_isScottContinuous (fun e t => Hstep H e t)
    (fun t => Hstep_isScottContinuous_e H t)

end DomainTheory.DataTypesAsLattices

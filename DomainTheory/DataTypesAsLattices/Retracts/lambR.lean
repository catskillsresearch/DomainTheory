module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.lambF
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lambR : Pomega := funOf Ycomb (graph lambF)

namespace lambR

theorem isRetract : Retract lambR :=
  (theorem_4_6.Limit lambF.isScottContinuous (fun _a ha =>
    plusR.isRetract intR.isRetract (arrowR.isRetract ha ha))).2

end lambR

end DomainTheory.DataTypesAsLattices

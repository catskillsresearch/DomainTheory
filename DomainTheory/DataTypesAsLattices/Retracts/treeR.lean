module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def treeR : Pomega := funOf Ycomb (graph treeF)

namespace treeR

theorem isRetract : Retract treeR :=
  (theorem_4_6.Limit treeF.isScottContinuous (fun _a ha =>
    plusR.isRetract bot_isRetract (tensorR.isRetract ha ha))).2

end treeR

end DomainTheory.DataTypesAsLattices

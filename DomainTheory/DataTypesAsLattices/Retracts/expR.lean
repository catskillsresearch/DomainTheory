module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.expF
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_6
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.tensor4
public import DomainTheory.DataTypesAsLattices.Retracts.plus7
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def expR : Pomega := funOf Ycomb (graph expF)

namespace expR

theorem isRetract : Retract expR :=
  (theorem_4_6.Limit expF.isScottContinuous (fun _a ha =>
    plus7.isRetract intR.isRetract bot_isRetract ha ha
      (tensor4.isRetract ha ha ha ha) (tensorR.isRetract ha ha)
      (tensorR.isRetract intR.isRetract ha))).2

end expR

end DomainTheory.DataTypesAsLattices

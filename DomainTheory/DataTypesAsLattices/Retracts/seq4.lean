module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Four-place sequence used by the expanded product of (4.44). -/
def seq4 (a b c d : Pomega) : Pomega :=
  graph (fun z =>
    condSet z a
      (condSet (predSet z) b
        (condSet (predSet (predSet z)) c
          (condSet (predSet (predSet (predSet z))) d botElem))))

end DomainTheory.DataTypesAsLattices

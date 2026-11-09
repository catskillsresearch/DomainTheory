module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexRhs

@[expose] public section

namespace DomainTheory.BridgeTheorems

noncomputable def sexDomainEquationIso :
    SexSys.Element ≃o SexRhs.Element :=
  treeDomainIso lowerBoundSystem

end DomainTheory.BridgeTheorems

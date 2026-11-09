module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

theorem exists_sexDomainEquationIso :
    Nonempty (SexSys.Element ≃o SexRhs.Element) :=
  ⟨sexDomainEquationIso⟩

end DomainTheory.BridgeTheorems

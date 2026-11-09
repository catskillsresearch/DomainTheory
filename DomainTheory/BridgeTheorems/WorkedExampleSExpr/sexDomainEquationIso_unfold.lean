module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems.InfoSys

theorem sexDomainEquationIso_unfold (x : SexSys.Element) :
    (sexDomainEquationIso x).carrier =
      treeUnfold lowerBoundSystem '' x.carrier :=
  rfl

end DomainTheory.BridgeTheorems

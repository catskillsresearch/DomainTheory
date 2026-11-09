module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems.InfoSys

theorem sexDomainEquationIso_fold (y : SexRhs.Element) :
    (sexDomainEquationIso.symm y).carrier =
      treeUnfold lowerBoundSystem ⁻¹' y.carrier :=
  rfl

end DomainTheory.BridgeTheorems

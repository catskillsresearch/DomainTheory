module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexRhs

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open Order

noncomputable def sexDomainEquationIso :
    SexSys.Element ≃o SexRhs.Element :=
  treeDomainIso lowerBoundSystem

end DomainTheory.BridgeTheorems

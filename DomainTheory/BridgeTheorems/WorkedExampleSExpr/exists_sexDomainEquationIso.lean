module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

theorem exists_sexDomainEquationIso :
    Nonempty (SexSys.Element ≃o SexRhs.Element) :=
  ⟨sexDomainEquationIso⟩

end DomainTheory.BridgeTheorems

module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

theorem exists_sexIdealIso :
    Nonempty (SexSys.Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement SexSys)) :=
  ⟨sexIdealIso⟩

end DomainTheory.BridgeTheorems

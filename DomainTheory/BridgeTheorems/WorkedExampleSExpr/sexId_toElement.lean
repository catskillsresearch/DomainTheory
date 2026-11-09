module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

theorem sexId_toElement (x : SexSys.Element) :
    sexIdScottContinuous.toFun x = x :=
  idMap.toElement SexSys x

end DomainTheory.BridgeTheorems

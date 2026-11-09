module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexSys

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys
open treeSystem

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open Order

abbrev SexRhs : InfoSys (SumToken ℕ (ProdToken SexSys SexSys)) :=
  treeRhs lowerBoundSystem

end DomainTheory.BridgeTheorems

module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexSys

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

abbrev SexRhs : InfoSys (SumToken ℕ (ProdToken SexSys SexSys)) :=
  treeRhs lowerBoundSystem

end DomainTheory.BridgeTheorems

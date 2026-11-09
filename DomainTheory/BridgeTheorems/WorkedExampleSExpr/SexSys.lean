module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.lowerBoundSystem

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

abbrev SexSys : InfoSys (TreeToken ℕ) :=
  treeSystem lowerBoundSystem

end DomainTheory.BridgeTheorems

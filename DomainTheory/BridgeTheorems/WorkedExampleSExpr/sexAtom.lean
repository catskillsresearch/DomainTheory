module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexSys

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

noncomputable def sexAtom (n : ℕ) : SexSys.Element :=
  SexSys.closure {TreeToken.atom n} (SexSys.con_sing _)

end DomainTheory.BridgeTheorems

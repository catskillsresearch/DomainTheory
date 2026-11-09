module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

theorem exists_sexNeighborhoodIso :
    Nonempty (SexSys.Element ≃o
      (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element) :=
  ⟨sexNeighborhoodIso⟩

end DomainTheory.BridgeTheorems

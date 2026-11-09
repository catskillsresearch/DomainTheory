module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

theorem exists_sexNeighborhoodIso :
    Nonempty (SexSys.Element ≃o
      (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element) :=
  ⟨sexNeighborhoodIso⟩

end DomainTheory.BridgeTheorems

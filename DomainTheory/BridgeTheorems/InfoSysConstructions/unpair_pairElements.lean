module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem unpair_pairElements (x : A.Element) (y : B.Element) :
    unpair A B (pairElements A B x y) = (x, y) := by
  simp [unpair, fstMap_pairElements, sndMap_pairElements]

end InfoSysConstructions

end DomainTheory.BridgeTheorems

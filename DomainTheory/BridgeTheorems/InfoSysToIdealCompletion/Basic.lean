module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.domainOrderIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open Order

noncomputable abbrev infoSys_to_idealCompletion {α : Type*} [DecidableEq α] (A : InfoSys α) :
    A.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  InfoSysToIdealCompletion.domainOrderIso A

/-- 1982 information-system elements → 1972 algebraic carrier (ideals of finite elements). -/
noncomputable abbrev bridge_1982_1972 := @infoSys_to_idealCompletion

end DomainTheory.BridgeTheorems

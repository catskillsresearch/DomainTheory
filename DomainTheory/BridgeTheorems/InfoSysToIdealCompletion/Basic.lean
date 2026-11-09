module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.domainOrderIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

end InfoSysToIdealCompletion

noncomputable abbrev infoSys_to_idealCompletion {α : Type*} [DecidableEq α] (A : InfoSys α) :
    A.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  InfoSysToIdealCompletion.domainOrderIso A
end DomainTheory.BridgeTheorems

module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.exists_assembleSum_eq

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

noncomputable def classifySum (z : (sumSystem A B).Element) :
    WithBot (A.Element ⊕ B.Element) :=
  Classical.choose (exists_assembleSum_eq A B z)

end InfoSysConstructions

end DomainTheory.BridgeTheorems

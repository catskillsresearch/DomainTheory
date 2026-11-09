module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.productDomainIso
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumDomainIso
public import DomainTheory.BridgeTheorems.InfoSysConstructions.functionSpaceDomainIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.InfoSys

noncomputable abbrev infoSys_product_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    A.Element × B.Element ≃o (productSystem A B).Element :=
  InfoSysConstructions.productDomainIso A B

noncomputable abbrev infoSys_sum_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element :=
  InfoSysConstructions.sumDomainIso A B

noncomputable abbrev infoSys_function_space_domain_equiv {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o (functionSystem A B).Element :=
  InfoSysConstructions.functionSpaceDomainIso A B
end DomainTheory.BridgeTheorems

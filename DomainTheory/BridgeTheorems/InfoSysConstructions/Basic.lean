module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.productDomainIso
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumDomainIso
public import DomainTheory.BridgeTheorems.InfoSysConstructions.functionSpaceDomainIso
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair_pairElements
public import DomainTheory.BridgeTheorems.InfoSysConstructions.pairElements_unpair
public import DomainTheory.BridgeTheorems.InfoSysConstructions.pairElements_mono
public import DomainTheory.BridgeTheorems.InfoSysConstructions.rhtFinset_singleton_left
public import DomainTheory.BridgeTheorems.InfoSysConstructions.lftFinset_singleton_right
public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumElementLft_inlMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumElementRht_inrMap_toElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inlMap_toElement_injective
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inrMap_toElement_injective
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sum_element_trichotomy
public import DomainTheory.BridgeTheorems.InfoSysConstructions.exists_assembleSum_eq
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.not_left_mem_sum_botElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.not_right_mem_sum_botElement
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_injective
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum_assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inlMap_toElement_le_iff
public import DomainTheory.BridgeTheorems.InfoSysConstructions.inrMap_toElement_le_iff
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum_mono
public import DomainTheory.BridgeTheorems.InfoSysConstructions.instPartialOrderApproximableMap
public import DomainTheory.BridgeTheorems.InfoSysConstructions.approxMap_toElement_le_iff

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

end InfoSysConstructions

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

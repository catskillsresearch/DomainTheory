module

public import DomainTheory.BridgeTheorems.InfoSysConstructions.instPartialOrderApproximableMap
public import DomainTheory.BridgeTheorems.InfoSysConstructions.approxMap_toElement_le_iff
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement_element_toApproxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

noncomputable def functionSpaceDomainIso :
    ApproximableMap A B ≃o (functionSystem A B).Element where
  toFun := approxMap_toElement A B
  invFun := element_toApproxMap A B
  left_inv := element_toApproxMap.approxMap_toElement A B
  right_inv := approxMap_toElement_element_toApproxMap A B
  map_rel_iff' := by
    intro f g
    exact approxMap_toElement_le_iff A B

end InfoSysConstructions

end DomainTheory.BridgeTheorems

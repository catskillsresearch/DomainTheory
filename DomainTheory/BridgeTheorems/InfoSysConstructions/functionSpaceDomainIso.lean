/-ai
The function-space domain isomorphism identifies approximable maps from an information system A to an information system B with elements of the function-space system. It sends a map to its associated element and an element to its associated approximable map. The two composites are the identities given by the round trips of Theorem 7.2, and the forward map reflects the pointwise order by the comparison of associated elements.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
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

/-- **Function-space domain iso (1982, Thm 7.2).** `|A → B| ≃o ApproximableMap A B`. -/
noncomputable def functionSpaceDomainIso :
    ApproximableMap A B ≃o (functionSystem A B).Element where
  toFun := approxMap_toElement A B
  invFun := element_toApproxMap A B
  left_inv := element_toApproxMap_approxMap_toElement A B
  right_inv := approxMap_toElement_element_toApproxMap A B
  map_rel_iff' := by
    intro f g
    exact approxMap_toElement_le_iff A B

end InfoSysConstructions

end DomainTheory.BridgeTheorems

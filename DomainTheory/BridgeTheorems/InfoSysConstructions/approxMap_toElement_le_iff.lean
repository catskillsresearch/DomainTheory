/-ai
For approximable maps f and g, the element associated with f lies under the element associated with g if and only if f lies under g in the pointwise relation order.

If the elements are ordered and f relates a token u to a token v, the corresponding function token lies in the carrier of the element of f and hence in the carrier of the element of g, so g relates u to v. Conversely, if f lies under g and a token lies in the carrier of the element of f, that token records a relation of f and therefore of g, so it lies in the carrier of the element of g.
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

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_approxMap_toElement
@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem approxMap_toElement_le_iff {f g : ApproximableMap A B} :
    approxMap_toElement A B f ≤ approxMap_toElement A B g ↔ f ≤ g := by
  constructor
  · intro h u v hrel
    have hp : mkFunToken A B u v (f.rel_dom hrel) (f.rel_cod hrel) ∈
        (approxMap_toElement A B f).carrier :=
      (mem_approxMap_toElement A B f).2 hrel
    exact (mem_approxMap_toElement A B g).1 (h hp)
  · intro hfg p hp
    exact (mem_approxMap_toElement A B g).2 (hfg ((mem_approxMap_toElement A B f).1 hp))

end InfoSysConstructions

end DomainTheory.BridgeTheorems

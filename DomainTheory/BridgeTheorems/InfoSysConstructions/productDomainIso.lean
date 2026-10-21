/-ai
The product domain isomorphism identifies a pair of elements of information systems A and B with an element of their product system, sending a pair to the paired element and an element to the pair of its projections. The two composites are the identities. The forward map reflects order because the first and second projections of an inequality of paired elements recover the two component inequalities, and it preserves order by monotonicity of pairing.
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
public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair
public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair_pairElements
public import DomainTheory.BridgeTheorems.InfoSysConstructions.pairElements_unpair
public import DomainTheory.BridgeTheorems.InfoSysConstructions.pairElements_mono

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- **Product domain iso (1982).** `|A × B| ≃o |A| × |B|`. -/
noncomputable def productDomainIso :
    A.Element × B.Element ≃o (productSystem A B).Element where
  toFun := fun p => pairElements A B p.1 p.2
  invFun := unpair A B
  left_inv := fun p => unpair_pairElements A B p.1 p.2
  right_inv := pairElements_unpair A B
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      change pairElements A B p.1 p.2 ≤ pairElements A B q.1 q.2 at h
      constructor
      · have hp := (fstMap A B).toElement_mono h
        rw [fstMap_pairElements A B p.1 p.2, fstMap_pairElements A B q.1 q.2] at hp
        exact hp
      · have hp := (sndMap A B).toElement_mono h
        rw [sndMap_pairElements A B p.1 p.2, sndMap_pairElements A B q.1 q.2] at hp
        exact hp
    · intro h
      exact pairElements_mono A B h.1 h.2

end InfoSysConstructions

end DomainTheory.BridgeTheorems

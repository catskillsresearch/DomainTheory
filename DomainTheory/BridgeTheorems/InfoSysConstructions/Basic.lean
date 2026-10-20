/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.unpair
public import DomainTheory.BridgeTheorems.InfoSysConstructions.productDomainIso
public import DomainTheory.BridgeTheorems.InfoSysConstructions.assembleSum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.classifySum
public import DomainTheory.BridgeTheorems.InfoSysConstructions.sumDomainIso
public import DomainTheory.BridgeTheorems.InfoSysConstructions.functionSpaceDomainIso
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

/-!
# Construction equivalence — products, separated sums, and function spaces

* **Product:** `|A × B| ≃o |A| × |B|` via `pairElements` / projections (Prop 6.2).
* **Separated sum:** `|A + B| ≃o WithBot (|A| ⊕ |B|)` via `inl`/`inr` (Prop 6.4).
  Classification of sum elements uses classical case-split on token polarity
  (`Classical.choice` in the footprint).
* **Function space:** `|A → B| ≃o ApproximableMap A B` via Theorem 7.2
  `approxMap_toElement` / `element_toApproxMap`.

1972 counterpart: products of continuous lattices (`proposition_2_9_a`); function space
Thm 3.3 in the sibling package.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)






/-! ## Separated sum `|A + B| ≃o WithBot (|A| ⊕ |B|)` -/






















/-! ## Function space `|A → B| ≃o ApproximableMap A B` -/




end InfoSysConstructions

/-- Blueprint-facing name for the 1982 product domain isomorphism. -/
noncomputable abbrev infoSys_product_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    A.Element × B.Element ≃o (productSystem A B).Element :=
  InfoSysConstructions.productDomainIso A B

/-- Blueprint-facing name for the 1982 separated-sum domain isomorphism (classical). -/
noncomputable abbrev infoSys_sum_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element :=
  InfoSysConstructions.sumDomainIso A B

/-- Blueprint-facing name for the 1982 function-space domain isomorphism. -/
noncomputable abbrev infoSys_function_space_domain_equiv {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o (functionSystem A B).Element :=
  InfoSysConstructions.functionSpaceDomainIso A B
end DomainTheory.BridgeTheorems

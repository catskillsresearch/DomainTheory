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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.instPartialOrderApproximableMap

@[expose] public section

set_option linter.unusedSectionVars false

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

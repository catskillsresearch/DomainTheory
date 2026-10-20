/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.botFinite
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.domainOrderIso
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.isFinite_bot
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_of_mem_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.nonempty_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.directed_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.isLowerSet_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.nonempty_idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.directed_idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_ofIdeal_of_mem
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal_toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal_ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal_mono

@[expose] public section

/-!
# Information systems → ideal completion (1982 → algebraic dcpo)

The domain `|A|` of an information system is the **ideal completion** of its
poset of finite elements `ū` (closures of consistent finite token sets):
`A.Element ≃o Order.Ideal (FiniteElement A)`.

Packaging of Factoids 4.4–4.5 (`directedSup`, algebraicity, `compact_closure`).
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)




















end InfoSysToIdealCompletion

/-- Blueprint name: `|A|` as the ideal completion of its finite elements. -/
noncomputable abbrev infoSys_to_idealCompletion {α : Type*} [DecidableEq α] (A : InfoSys α) :
    A.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  InfoSysToIdealCompletion.domainOrderIso A
end DomainTheory.BridgeTheorems

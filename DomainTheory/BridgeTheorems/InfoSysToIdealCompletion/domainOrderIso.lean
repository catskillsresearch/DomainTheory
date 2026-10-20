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
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.FiniteElement
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_ofIdeal_of_mem
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal_toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal_ofIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Order isomorphism: domain elements ↔ ideals of finite elements. -/
noncomputable def domainOrderIso : A.Element ≃o Ideal (FiniteElement A) where
  toFun := toIdeal A
  invFun := ofIdeal A
  left_inv := ofIdeal_toIdeal A
  right_inv := toIdeal_ofIdeal A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      -- x ≤ y from toIdeal x ≤ toIdeal y via algebraicity
      rw [← ofIdeal_toIdeal A x, ← ofIdeal_toIdeal A y]
      refine A.directedSup_le _ _ _ ?_
      intro z hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact le_ofIdeal_of_mem A (h hz')
    · exact toIdeal_mono A

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.interOf_insert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- If a neighbourhood sits below `interOf u`, then `interOf u ∈ 𝒟`. -/
theorem interOf_mem_of_lower_bound {u : Finset ι} {Z : Set α}
    (hZ : B.system.mem Z) (hsub : Z ⊆ B.interOf u) : B.system.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using B.system.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha] at hsub ⊢
    have hs : B.system.mem (B.interOf s) := ih (hsub.trans Set.inter_subset_right)
    exact B.system.inter_mem (B.nbhd_mem a) hs hZ hsub

end NbhdBasis

end DomainTheory.BridgeTheorems

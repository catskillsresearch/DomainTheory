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

/-- A filter containing every `nbhd i` for `i ∈ u` contains `interOf u`. -/
theorem filter_mem_interOf (x : B.system.Element) {u : Finset ι}
    (hu : ∀ i ∈ u, x.mem (B.nbhd i)) : x.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using x.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha]
    exact x.inter_mem (hu a (Finset.mem_insert_self a s))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

end NbhdBasis

end DomainTheory.BridgeTheorems

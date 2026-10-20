/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.basicOpen_empty
public import DomainTheory.BridgeTheorems.basicOpen_singleton_inter
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_basicOpen_of_singletons (f : (toNeighborhoodSystem A).Element) {Y : Finset α}
    (hY : ∀ a ∈ Y, f.mem (A.basicOpen ({a} : Finset α))) :
    f.mem (A.basicOpen Y) := by
  induction Y using Finset.induction with
  | empty =>
    rw [basicOpen_empty]
    have hmaster : (toNeighborhoodSystem A).master = (Set.univ : Set A.Element) := rfl
    rw [← hmaster]
    exact f.master_mem
  | insert a s _ha ih =>
    have hA := hY a (Finset.mem_insert_self a s)
    have hSm := ih fun i hi => hY i (Finset.mem_insert_of_mem hi)
    simpa [basicOpen_singleton_inter A a s] using f.inter_mem hA hSm

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems

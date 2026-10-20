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
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid46
public import DomainTheory.InformationSystems.Proposition23

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem funion_singleton_eq_insert (a : α) (s : Finset α) :
    ({a} : Finset α) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))
    · exact Finset.mem_insert_of_mem h
  · intro hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (h ▸ Finset.mem_singleton_self a))
    · exact mem_funion.mpr (Or.inr h)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems

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
public import DomainTheory.BridgeTheorems.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.toFilter
public import DomainTheory.BridgeTheorems.ofFilter
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood.domainOrderIso
public import DomainTheory.BridgeTheorems.basicOpen_empty
public import DomainTheory.BridgeTheorems.mem_basicOpen_singleton
public import DomainTheory.BridgeTheorems.funion_singleton_eq_insert
public import DomainTheory.BridgeTheorems.basicOpen_singleton_inter
public import DomainTheory.BridgeTheorems.ent_of_basicOpen_subset
public import DomainTheory.BridgeTheorems.con_of_basicOpen_subset
public import DomainTheory.BridgeTheorems.mem_basicOpen_of_singletons
public import DomainTheory.BridgeTheorems.mem_basicOpen_iff
public import DomainTheory.BridgeTheorems.toFilter_ofFilter
public import DomainTheory.BridgeTheorems.ofFilter_toFilter

@[expose] public section

/-!
# Information systems → neighbourhood systems (1982 → 1980)

Scott (1982, §4): for `u ∈ Con`, the basic open
`[u] = { x ∈ |A| | u ⊆ x }` yields a neighbourhood system on the domain `|A|`
whose filters recover the original elements. This is the converse direction to
`NeighborhoodToInfoSys`.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems
open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)















end InfoSysToNeighborhood

/-- Blueprint-facing name for the 1982 → 1980 basic-open neighbourhood system. -/
abbrev infoSys_to_neighborhoodSystem {α : Type*} [DecidableEq α] (A : InfoSys α) :
    NeighborhoodSystem A.Element :=
  InfoSysToNeighborhood.toNeighborhoodSystem A

end DomainTheory.BridgeTheorems

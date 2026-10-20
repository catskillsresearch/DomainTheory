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
public import DomainTheory.BridgeTheorems.con_of_basicOpen_subset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- **`infoSys_to_neighborhoodSystem`.** -/
def toNeighborhoodSystem : NeighborhoodSystem A.Element where
  mem X := ∃ u, u ∈ A.Con ∧ X = A.basicOpen u
  master := Set.univ
  master_nonempty := ⟨A.closure ∅ A.con_empty, Set.mem_univ _⟩
  master_mem := ⟨∅, A.con_empty, (basicOpen_empty A).symm⟩
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    obtain ⟨u, hu, rfl⟩ := hX
    obtain ⟨v, hv, rfl⟩ := hY
    obtain ⟨w, hw, rfl⟩ := hZ
    have hsub : A.basicOpen w ⊆ A.basicOpen (u ∪' v) := by
      intro x hx
      have hx' : x ∈ A.basicOpen u ∩ A.basicOpen v := hZsub hx
      rwa [basicOpen_inter A] at hx'
    have huv : u ∪' v ∈ A.Con := con_of_basicOpen_subset A hw hsub
    exact ⟨u ∪' v, huv, basicOpen_inter A u v⟩
  sub_master := fun {_} _ => Set.subset_univ _

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems

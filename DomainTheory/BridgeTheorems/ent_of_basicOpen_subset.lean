module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem ent_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) {a : α} (ha : a ∈ u) : A.Ent w a := by
  have : A.closure w hw ∈ A.basicOpen w := subset_closure A hw
  have hU : A.closure w hw ∈ A.basicOpen u := hsub this
  exact hU (Finset.mem_coe.2 ha)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems

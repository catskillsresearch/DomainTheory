module
public import DomainTheory.BridgeTheorems.ent_of_basicOpen_subset
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.basicOpen
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
public import DomainTheory.InformationSystems.InformationSystems.Constructive.subset_funion_right
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23


@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem con_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) : u ∈ A.Con := by
  have hEnt : A.EntSet w u := fun a ha => ent_of_basicOpen_subset A hw hsub ha
  exact A.con_subset (proposition_2_3_ii A hw hEnt) (subset_funion_right _ _)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems

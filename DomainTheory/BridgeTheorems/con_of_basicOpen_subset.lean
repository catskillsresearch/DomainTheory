/-ai
If a consistent finite set w has its basic open contained in the basic open of a finite set u, then u is consistent.

Every token of u is entailed by w. The second clause of Proposition 2.3 therefore puts the formal union of w with u among the consistent sets, and u is contained in that formal union.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.ent_of_basicOpen_subset

public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
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

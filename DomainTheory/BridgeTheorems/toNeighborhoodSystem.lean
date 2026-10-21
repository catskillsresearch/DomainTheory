/-ai
The map toNeighborhoodSystem turns an information system into the neighbourhood system on its elements whose neighbourhoods are the basic opens of consistent finite sets, with the set of all elements as master set. The master set is the basic open of the empty set, and it contains the closure of the empty set. The intersection of two basic opens is the basic open of their fused union; that union is consistent whenever a third basic open lies inside the intersection, because that third open is then contained in the basic open of the union. Every neighbourhood is contained in the master set.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.basicOpen_empty
public import DomainTheory.BridgeTheorems.con_of_basicOpen_subset

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.basicOpen_inter
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

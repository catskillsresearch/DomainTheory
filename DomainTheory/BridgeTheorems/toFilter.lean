/-ai
The map toFilter sends an information-system element to the filter of those basic opens that come from a consistent finite set contained in the element's carrier. Such a basic open belongs to the neighbourhood system by its witnessing set. The master set is the basic open of the empty set. The intersection of two such basic opens is the basic open of their fused union, which is consistent because it is contained in the carrier. If the basic open of one consistent set is contained in the basic open of another, each token of the second is entailed by the first and therefore lies in the carrier by closure.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.basicOpen_empty
public import DomainTheory.BridgeTheorems.ent_of_basicOpen_subset
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

def toFilter (x : A.Element) : (toNeighborhoodSystem A).Element where
  mem U := ∃ u, u ∈ A.Con ∧ U = A.basicOpen u ∧ ↑u ⊆ x.carrier
  sub := by
    intro U h
    obtain ⟨u, hu, rfl, _⟩ := h
    exact ⟨u, hu, rfl⟩
  master_mem := ⟨∅, A.con_empty, (basicOpen_empty A).symm, by
    intro a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))⟩
  inter_mem := by
    intro U V hU hV
    obtain ⟨u, hu, rfl, huX⟩ := hU
    obtain ⟨v, hv, rfl, hvX⟩ := hV
    refine ⟨u ∪' v, ?_, basicOpen_inter A u v, ?_⟩
    · have hsub : ↑(u ∪' v) ⊆ x.carrier := by
        intro a ha
        rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
        · exact huX (Finset.mem_coe.2 h)
        · exact hvX (Finset.mem_coe.2 h)
      exact x.consistent (u ∪' v) hsub
    · intro a ha
      rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
      · exact huX (Finset.mem_coe.2 h)
      · exact hvX (Finset.mem_coe.2 h)
  up_mem := by
    intro U V hU hV hUV
    obtain ⟨u, hu, rfl, huX⟩ := hU
    obtain ⟨v, hv, rfl⟩ := hV
    refine ⟨v, hv, rfl, ?_⟩
    intro a ha
    exact x.closed u a huX (ent_of_basicOpen_subset A hu hUV ha)

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems

/-ai
Example 1.3 is the neighbourhood system on the tokens {0, 1, 2}. Membership is the membership predicate of the example, the master neighbourhood is the whole token set, which is nonempty and belongs to the system, every neighbourhood is contained in the whole set, and the intersection of two neighbourhoods is again a neighbourhood because that intersection equals the master neighbourhood, {1, 2}, or {2}, each of which belongs to the system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.inter_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- **Example 1.3.** The neighbourhood system on `Δ = {0, 1, 2}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_twelve
    · rw [h]; exact mem_two

end DomainTheory.NeighbourhoodSystems.Example13

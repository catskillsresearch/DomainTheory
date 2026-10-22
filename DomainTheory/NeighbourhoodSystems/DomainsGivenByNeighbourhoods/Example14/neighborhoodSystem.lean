module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.not_mem_empty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.inter_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- **Example 1.4.** The binary-tree neighbourhood system on `Δ = {Λ,0,1,00,01,10,11}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h | h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_left
    · rw [h]; exact mem_right
    · rw [h]; exact mem_leaf00
    · rw [h]; exact mem_leaf01
    · rw [h]; exact mem_leaf10
    · rw [h]; exact mem_leaf11
    · rw [h] at hZsub
      have hz : Z = (∅ : Set Token) := Set.subset_empty_iff.mp hZsub
      subst hz
      exact absurd hZ not_mem_empty

end DomainTheory.NeighbourhoodSystems.Example14

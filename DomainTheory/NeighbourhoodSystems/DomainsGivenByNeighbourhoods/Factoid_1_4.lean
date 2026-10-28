module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems

def NeighborhoodSystem.ofNestedOrDisjoint {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master) (hnd : NestedOrDisjoint mem)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master) : NeighborhoodSystem α where
  mem
  master
  master_nonempty
  master_mem
  sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases hnd hX hY with h | h | h
    · rwa [Set.inter_eq_left.mpr h]
    · rwa [Set.inter_eq_right.mpr h]
    · rw [h]
      rw [h] at hZsub
      rwa [← Set.subset_empty_iff.mp hZsub]

end DomainTheory.NeighbourhoodSystems
end

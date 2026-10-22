/-ai
The non-positive system is the neighbourhood system on the three tokens whose neighbourhoods are the master and the two overlapping sets. The master is the whole token set, which is nonempty and a neighbourhood, and every neighbourhood is contained in it. The intersection of two neighbourhoods is the master, one of the two overlapping sets, or the singleton of the middle token. The first three of these are neighbourhoods, and the last case cannot occur because no neighbourhood is contained in that singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Tok
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_b
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.not_mem_sub_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.inter_eq

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- **Exercise 1.19 — the non-positive example is a neighbourhood system.** The only intersection
that is not already a neighbourhood is `{0,1} ∩ {1,2} = {1}`, and that case is impossible: a
consistency witness `Z ⊆ {1}` with `Z ∈ 𝒟` does not exist (`not_mem_sub_one`). -/
def notPositiveSystem : NeighborhoodSystem Tok where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_a
    · rw [h]; exact mem_b
    · rw [h] at hZsub; exact (not_mem_sub_one hZ hZsub).elim

end DomainTheory.NeighbourhoodSystems.Exercise119

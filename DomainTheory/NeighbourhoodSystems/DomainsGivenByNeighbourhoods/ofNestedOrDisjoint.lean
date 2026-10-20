module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **Factoid 1.4a (Scott 1981, PRG-19).** "In these systems two neighbourhoods are either
disjoint or one is included in the other": a family containing `Δ` whose members are pairwise
nested-or-disjoint **is** a neighbourhood system. This uniformly explains why Examples 1.2,
1.3 and 1.4 satisfy Definition 1.1.

The verification of condition (ii) needs no choice: if `X, Y` are nested then `X ∩ Y` is the
smaller (already in `𝒟`); if they are disjoint then the consistency witness `Z ⊆ X ∩ Y = ∅`
forces `Z = ∅`, whence `X ∩ Y = ∅ = Z ∈ 𝒟`. The caller supplies `master_nonempty`
(Scott's standing `Δ ≠ ∅` assumption) and `sub_master` (`𝒟 ⊆ 𝒫(Δ)`) directly. -/
def NeighborhoodSystem.ofNestedOrDisjoint {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master) (hnd : NestedOrDisjoint mem)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master) : NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases hnd hX hY with h | h | h
    · rwa [Set.inter_eq_left.mpr h]
    · rwa [Set.inter_eq_right.mpr h]
    · rw [h]
      rw [h] at hZsub
      rwa [← Set.subset_empty_iff.mp hZsub]

end DomainTheory.NeighbourhoodSystems

/-ai
The total element at the leaf 00 consists of the master neighbourhood, the left branch, and the leaf 00. Each of these is a neighbourhood, the master neighbourhood belongs to the element, the intersection of any two is again one of the three, and a neighbourhood containing one of them is again one of the three, by the master-subset lemma and the subset cases for the left branch and for the leaf 00.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.neighborhoodSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, left, leaf00}` (leaf `00`). -/
def elem00 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf00
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf00
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf00)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf00_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf00_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14

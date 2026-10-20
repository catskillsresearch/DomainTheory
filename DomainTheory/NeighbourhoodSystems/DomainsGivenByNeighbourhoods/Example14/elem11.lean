module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.neighborhoodSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, right, leaf11}` (leaf `11`). -/
def elem11 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf11
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf11
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf11)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf11_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf11_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14

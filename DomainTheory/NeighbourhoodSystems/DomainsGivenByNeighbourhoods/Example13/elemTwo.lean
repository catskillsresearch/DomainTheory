module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve_inter_two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two_inter_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.neighborhoodSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, {1,2}, {2}}`. -/
def elemTwo : neighborhoodSystem.Element where
  mem X := X = master ∨ X = twelve ∨ X = two
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr (twelve_inter_two))
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr (two_inter_twelve))
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example13

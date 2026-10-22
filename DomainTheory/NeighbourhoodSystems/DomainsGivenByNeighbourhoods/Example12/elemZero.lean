/-ai
The total element of Example 1.2 determined by {0} is the filter whose neighbourhoods are the master and {0}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero_not_subset_one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.neighborhoodSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element determined by `{0}`. -/
def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = zero
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_zero
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hXY zero_not_subset_one

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example12

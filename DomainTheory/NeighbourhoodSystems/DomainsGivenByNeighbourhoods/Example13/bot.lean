module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.neighborhoodSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The bottom element `⊥ = {Δ}`. -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    intro X Y hX hY
    rw [hX, hY, master_inter]
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example13

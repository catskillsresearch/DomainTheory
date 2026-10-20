module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem mem_master : mem master := by simp [mem, memSet, master, zero, one]

end DomainTheory.NeighbourhoodSystems.Example12

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem mem_twelve : mem twelve := by simp [mem, memSet, master, twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13

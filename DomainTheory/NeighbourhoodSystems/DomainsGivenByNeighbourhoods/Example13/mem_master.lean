/-ai
The master neighbourhood belongs to the neighbourhood system of Example 1.3.

Unfold membership, the set of neighbourhoods, and the three neighbourhood definitions.
ai-/
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

theorem mem_master : mem master := by simp [mem, memSet, master, twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13

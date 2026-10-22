module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf11

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- A neighbourhood of Example 1.4 is exactly one of the seven. -/
theorem mem_iff (X : Set Token) :
    mem X ↔ X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X = leaf11 := by
  constructor
  · intro h
    simpa [mem, memSet] using h
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_right
    · exact mem_leaf00
    · exact mem_leaf01
    · exact mem_leaf10
    · exact mem_leaf11

end DomainTheory.NeighbourhoodSystems.Example14

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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem eq_of_master_subset {Y : Set Token} (hY : mem Y) (h : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [left])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [right])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf00])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf01])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf10])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14

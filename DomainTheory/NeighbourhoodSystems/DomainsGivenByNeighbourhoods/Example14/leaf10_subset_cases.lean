module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
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

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf10 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf10 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [left])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf00])
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf01])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14

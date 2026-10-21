/-ai
A neighbourhood containing the leaf 01 is the master neighbourhood, the left branch, or the leaf 01.

Classify the neighbourhood. The master neighbourhood, the left branch, and the leaf 01 are the three stated cases. In each of the other four cases the token 4, which belongs to the leaf 01, fails to belong to the neighbourhood.
ai-/
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

theorem leaf01_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf01 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf01 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [right])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf00])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf10])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14

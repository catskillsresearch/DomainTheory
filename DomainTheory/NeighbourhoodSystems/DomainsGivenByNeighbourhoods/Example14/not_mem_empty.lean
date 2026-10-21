/-ai
The empty set of tokens is not a neighbourhood of the binary tree.

Assume that it is. The membership characterization writes it as the master, the left subtree, the right subtree, or one of the four leaves. Each of those sets contains one of the tokens 0 through 6, which cannot lie in the empty set.
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

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h | h | h | h | h
  · have : (0 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [master]
    simp at this
  · have : (1 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [left]
    simp at this
  · have : (2 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [right]
    simp at this
  · have : (3 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf00]
    simp at this
  · have : (4 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf01]
    simp at this
  · have : (5 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf10]
    simp at this
  · have : (6 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf11]
    simp at this

end DomainTheory.NeighbourhoodSystems.Example14

/-ai
A set of tokens is a neighbourhood of Example 1.3 exactly when it equals the master neighbourhood, {1, 2}, or {2}.

In one direction, unfold membership and the three neighbourhoods and split into those three cases. In the other direction, each equality is the corresponding membership lemma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.mem_two

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- A neighbourhood of Example 1.3 is exactly one of `Δ`, `{1,2}`, or `{2}`. -/
theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = twelve ∨ X = two := by
  constructor
  · intro h
    simp [mem, memSet, master, twelve, two] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two

end DomainTheory.NeighbourhoodSystems.Example13

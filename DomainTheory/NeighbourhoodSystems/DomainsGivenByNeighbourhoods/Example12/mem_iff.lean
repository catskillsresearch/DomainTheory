/-ai
A set is a neighbourhood of Example 1.2 if and only if it is the master, {0}, or {1}.

Membership in the three-element set of neighbourhoods splits into those three equalities, and each of those three sets belongs to the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.mem_one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

/-- A neighbourhood of Example 1.2 is exactly one of `Δ`, `{0}`, or `{1}`. -/
theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = zero ∨ X = one := by
  constructor
  · intro h
    simp [mem, memSet, master, zero, one] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_zero
    · exact mem_one

end DomainTheory.NeighbourhoodSystems.Example12

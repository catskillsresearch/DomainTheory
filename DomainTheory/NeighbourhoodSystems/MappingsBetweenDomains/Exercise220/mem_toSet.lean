/-ai
A natural number lies in the set represented by an element if and only if the complement of its singleton belongs to the element.

The two sides are definitionally the same proposition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_toSet {x : powerSet.Element} {n : ℕ} : n ∈ toSet x ↔ x.mem ({n}ᶜ) := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise220

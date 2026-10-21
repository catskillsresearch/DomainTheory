/-ai
A set of natural numbers is a neighbourhood of the powerset system if and only if its complement is finite.

The two sides are definitionally the same proposition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_powerSet {X : Set ℕ} : powerSet.mem X ↔ Xᶜ.Finite := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise220

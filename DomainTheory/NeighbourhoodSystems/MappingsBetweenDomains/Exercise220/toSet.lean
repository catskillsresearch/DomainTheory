/-ai
The set of natural numbers represented by an element of the powerset domain consists of those numbers whose singleton complement belongs to the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The subset of `ℕ` represented by an element: `n ∈ toSet x ↔ {n}ᶜ ∈ x`. -/
def toSet (x : powerSet.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

end DomainTheory.NeighbourhoodSystems.Exercise220

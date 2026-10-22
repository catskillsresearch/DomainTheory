module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The subset of `ℕ` represented by an element: `n ∈ toSet x ↔ {n}ᶜ ∈ x`. -/
def toSet (x : powerSet.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

end DomainTheory.NeighbourhoodSystems.Exercise220

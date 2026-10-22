module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_toSet {x : powerSet.Element} {n : ℕ} : n ∈ toSet x ↔ x.mem ({n}ᶜ) := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise220

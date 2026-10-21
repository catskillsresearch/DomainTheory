/-ai
The filter of a set of natural numbers grows when the set grows.

A cofinite neighbourhood whose complement lies in the smaller set still has its complement in the larger set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.ofSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `ofSet` is monotone in the set. -/
theorem ofSet_mono {S S' : Set ℕ} (h : S ⊆ S') : ofSet S ≤ ofSet S' :=
  fun _ hZ => ⟨hZ.1, hZ.2.trans h⟩

end DomainTheory.NeighbourhoodSystems.Exercise220

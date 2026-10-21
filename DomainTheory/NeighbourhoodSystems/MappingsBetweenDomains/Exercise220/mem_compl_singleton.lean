/-ai
The complement of a singleton is a neighbourhood of the powerset system.

Its complement is a singleton, which is finite.
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

/-- The complement of a singleton is a neighbourhood (it represents the finite element `{n}`). -/
theorem mem_compl_singleton (n : ℕ) : powerSet.mem ({n}ᶜ) := by
  rw [mem_powerSet, compl_compl]; exact Set.finite_singleton n

end DomainTheory.NeighbourhoodSystems.Exercise220

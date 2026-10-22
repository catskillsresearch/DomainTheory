/-ai
The intersection of two neighbourhoods of the powerset system is a neighbourhood.

The complement of an intersection is the union of the complements, and the union of two finite sets is finite.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Cofinite sets are closed under intersection (witness-free form). -/
theorem powerSet_inter_mem {A B : Set ℕ} (hA : powerSet.mem A) (hB : powerSet.mem B) :
    powerSet.mem (A ∩ B) := by
  rw [mem_powerSet, Set.compl_inter]; exact hA.union hB

end DomainTheory.NeighbourhoodSystems.Exercise220

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `S − 1 = {n ∣ n + 1 ∈ S}`. -/
def predSet (S : Set ℕ) : Set ℕ := {n | n + 1 ∈ S}

end DomainTheory.NeighbourhoodSystems.Exercise220

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem powerSet_master : powerSet.master = (Set.univ : Set ℕ) := rfl

end DomainTheory.NeighbourhoodSystems.Exercise220

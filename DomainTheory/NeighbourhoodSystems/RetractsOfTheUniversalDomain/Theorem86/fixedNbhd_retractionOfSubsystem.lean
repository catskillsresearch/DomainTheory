/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- `fixedNbhd (retractionOfSubsystem h) = D`: the round trip recovering a subsystem `D` from the
retraction it induces. `Y (retractionOfSubsystem h) Y ↔ ∃W∈D, Y⊆W⊆Y`, and `Y⊆W⊆Y` forces `W=Y`, so
this says exactly `D.mem Y` (using `E.mem Y` for free from `D ⊆ E`). -/
theorem fixedNbhd_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    fixedNbhd (Subsystem.retractionOfSubsystem h) = D := by
  apply NeighborhoodSystem.ext
  · intro X
    rw [fixedNbhd_mem, Subsystem.retractionOfSubsystem_rel]
    constructor
    · rintro ⟨hXE, -, -, Y, hY, hXY, hYX⟩
      rw [Set.Subset.antisymm hXY hYX]
      exact hY
    · intro hX
      exact ⟨h.sub hX, h.sub hX, h.sub hX, X, hX, subset_rfl, subset_rfl⟩
  · exact h.master_eq.symm

end DomainTheory.NeighbourhoodSystems

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition82
public import DomainTheory.Neighborhood.Definition83.Basic
public import DomainTheory.Neighborhood.Definition83.isProjection_retractionOfSubsystem
public import DomainTheory.Neighborhood.Definition83.isFinitary_retractionOfSubsystem

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}




namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is a finitary projection** (Definition 8.3, both clauses). -/
theorem isFinitaryProjection_retractionOfSubsystem (h : D ◁ E) :
    IsFinitaryProjection (retractionOfSubsystem h) :=
  ⟨isProjection_retractionOfSubsystem h, isFinitary_retractionOfSubsystem h⟩

end Subsystem
end DomainTheory.Neighborhood

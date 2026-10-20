/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition82
import DomainTheory.Neighborhood.Definition83.Basic
import DomainTheory.Neighborhood.Definition83.retractionOfSubsystem_le_idMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}




namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is a projection** (Definition 8.3). -/
theorem isProjection_retractionOfSubsystem (h : D ◁ E) :
    IsProjection (retractionOfSubsystem h) :=
  ⟨isRetraction_retractionOfSubsystem h, retractionOfSubsystem_le_idMap h⟩

end Subsystem
end DomainTheory.Neighborhood

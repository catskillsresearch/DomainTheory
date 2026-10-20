/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition81
public import DomainTheory.Neighborhood.Proposition612
public import DomainTheory.Neighborhood.Proposition82.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem



/-- **Proposition 8.2, first half.** `retractionOfSubsystem h` is a retraction: `a ∘ a = a`, via
`a ∘ a = i∘(j∘i)∘j = i∘I_D∘j = i∘j = a`. -/
theorem isRetraction_retractionOfSubsystem (h : D ◁ E) :
    IsRetraction (retractionOfSubsystem h) := by
  show (h.inj.comp h.proj).comp (h.inj.comp h.proj) = h.inj.comp h.proj
  rw [comp_assoc, ← comp_assoc h.proj h.inj h.proj, h.proj_comp_inj, idMap_comp]

end Subsystem
end DomainTheory.Neighborhood

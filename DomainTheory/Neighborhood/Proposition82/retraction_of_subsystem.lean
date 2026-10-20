/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition81
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Proposition82.Basic
import DomainTheory.Neighborhood.Proposition82.isRetraction_retractionOfSubsystem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem





/-- **Proposition 8.2 (Scott 1981, PRG-19), packaged.** `D ◁ E` induces a retraction `a` on `E`
whose fixed-point set is (order-isomorphic to) `|D|`. -/
theorem retraction_of_subsystem (h : D ◁ E) :
    IsRetraction (retractionOfSubsystem h) ∧
      Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y}) :=
  ⟨isRetraction_retractionOfSubsystem h, ⟨elementIso h⟩⟩

end Subsystem
end DomainTheory.Neighborhood

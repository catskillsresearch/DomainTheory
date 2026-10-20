/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Proposition611
import DomainTheory.Neighborhood.Theorem86.Basic
import DomainTheory.Neighborhood.Theorem86.isRetraction_subApprox
import DomainTheory.Neighborhood.Theorem86.subApprox_le_idMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}









namespace Sub8_6















/-- **`sub` is itself a *projection* on the function space `(E → E)`** (half of Theorem 8.6's
second clause; the other half, `IsFinitary subApprox`, is below). -/
theorem isProjection_subApprox : IsProjection (subApprox (E := E)) :=
  ⟨isRetraction_subApprox, subApprox_le_idMap⟩

end Sub8_6
end DomainTheory.Neighborhood

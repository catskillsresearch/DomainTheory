/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Exercise625.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`h(g(x)) = x`.** The first projection-pair law `h ∘ g = I_𝒟`, read on elements. -/
theorem proj_inj_apply (P : ProjectionPair D E) (x : D.Element) :
    P.proj.toElementMap (P.inj.toElementMap x) = x := by
  rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]

end Subsystem.ProjectionPair
end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Exercise625.Basic
import DomainTheory.Neighborhood.Exercise625.proj_inj_apply


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair







/-- **Exercise 6.25 — "check that the set on the right is non-empty".** `g(x)` itself lies in
`{y ∣ x ⊑ h(y)}`, since `x ⊑ h(g(x)) = x`. -/
theorem upperSet_nonempty (P : ProjectionPair D E) (x : D.Element) :
    (P.upperSet x).Nonempty :=
  ⟨P.inj.toElementMap x, by rw [mem_upperSet, P.proj_inj_apply x]⟩

end Subsystem.ProjectionPair
end DomainTheory.Neighborhood

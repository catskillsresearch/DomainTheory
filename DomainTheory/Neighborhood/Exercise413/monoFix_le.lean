/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise118
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise413.Basic
import DomainTheory.Neighborhood.Exercise413.monoFix_le_preFix


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem





/-- `monoFix f ha ⊑ a`: the least fixed point lies below the given pre-fixed point `a`. -/
theorem monoFix_le (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) :
    monoFix f ha ≤ a := monoFix_le_preFix f ha ha

end NeighborhoodSystem
end DomainTheory.Neighborhood

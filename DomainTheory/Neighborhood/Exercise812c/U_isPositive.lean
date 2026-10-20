/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.IntervalPrimrec
import DomainTheory.Neighborhood.Theorem88
import DomainTheory.Neighborhood.Exercise812c.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem








/-- **`U` is Positive**: since `combineIntervals` presents *any* raw intersection of two presented
lists unconditionally, and `X ∩ Y ⊆ [0,1)` is automatic whenever `X ⊆ [0,1)`, only non-emptiness
can ever obstruct `U.mem (X ∩ Y)`. -/
theorem U_isPositive : U.IsPositive := by
  rintro X Y ⟨⟨L1, rfl⟩, -, hXsub⟩ ⟨⟨L2, rfl⟩, -, -⟩
  refine ⟨fun h => h.2.1, fun hne => ⟨⟨combineIntervals L1 L2, presentedIntervals_inter L1 L2⟩,
    hne, Set.inter_subset_left.trans hXsub⟩⟩

end DomainTheory.Neighborhood

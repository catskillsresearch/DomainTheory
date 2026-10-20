/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise823
import DomainTheory.Neighborhood.Exercise715
import DomainTheory.Neighborhood.Exercise825Pow
import DomainTheory.Neighborhood.Exercise825Embed
import DomainTheory.Neighborhood.Exercise825Closing
import DomainTheory.Neighborhood.Exercise820
import DomainTheory.Neighborhood.Exercise825FixedPoint.Basic
import DomainTheory.Neighborhood.Exercise825FixedPoint.isFinitaryProjection_cCombinator
import DomainTheory.Neighborhood.Exercise825FixedPoint.tOp_tOpMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap



















theorem hT_TArrow (a : ApproximableMap U U) (ha : IsFinitaryProjection a) :
    Nonempty (Exercise823.Fix (Exercise823.tOp (tOpMap cCombinator) a) ≃o
      (TArrow a).2.Element) := by
  rw [tOp_tOpMap]
  exact ⟨(arrowComb_elementIso a cCombinator ha isFinitaryProjection_cCombinator).symm⟩

end DomainTheory.Neighborhood

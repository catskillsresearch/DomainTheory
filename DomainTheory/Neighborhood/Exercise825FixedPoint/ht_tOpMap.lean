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
import DomainTheory.Neighborhood.Exercise825FixedPoint.tOp_tOpMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

















/-- **`t` sends finitary projections to finitary projections** (Exercise 8.23's hypothesis `ht`),
via `tOp_tOpMap` and Proposition 8.10(b)'s `finitaryProjection_arrowComb`. -/
theorem ht_tOpMap (c : ApproximableMap U U) (hc : IsFinitaryProjection c) :
    ∀ a, IsFinitaryProjection a → IsFinitaryProjection (Exercise823.tOp (tOpMap c) a) := by
  intro a ha
  rw [tOp_tOpMap]
  exact finitaryProjection_arrowComb a c ha hc

end DomainTheory.Neighborhood

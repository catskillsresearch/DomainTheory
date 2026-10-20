/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.Exercise412.Basic


namespace DomainTheory.Neighborhood.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem





/-- The two total elements are incomparable: `elemZero ⋢ elemOne`. -/
theorem elemZero_not_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h Example12.zero (Or.inr rfl) with hm | ho
  · exact zero_ne_master hm
  · exact one_ne_zero ho.symm

end DomainTheory.Neighborhood.Exercise412

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Approximable
public import DomainTheory.Neighborhood.Example12
public import DomainTheory.Neighborhood.Exercise412.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem





/-- The two total elements are incomparable: `elemOne ⋢ elemZero`. -/
theorem elemOne_not_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h Example12.one (Or.inr rfl) with hm | hz
  · exact one_ne_master hm
  · exact one_ne_zero hz

end DomainTheory.Neighborhood.Exercise412

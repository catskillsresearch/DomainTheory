/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419








/-- The base of the iterated bottom element: `f⁰(⊥) = ⊥`. -/
theorem iterElem_zero' {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) :
    f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

end DomainTheory.Neighborhood.Exercise516

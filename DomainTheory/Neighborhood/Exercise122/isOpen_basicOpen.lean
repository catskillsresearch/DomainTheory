/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Topology.Inseparable
import DomainTheory.Neighborhood.Exercise122.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- **Exercise 1.22.** Each basic neighbourhood `[X]` is open. -/
theorem isOpen_basicOpen (X : Set α) : IsOpen (V.basicOpen X) :=
  fun _ hx => ⟨X, hx, subset_rfl⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import Mathlib.Data.Set.Image
import DomainTheory.Neighborhood.ApproximableExercises.Basic
import DomainTheory.Neighborhood.ApproximableExercises.mem_iSupDirected


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem le_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) (i : I) :
    a i ≤ iSupDirected a hdir :=
  fun _ hZ => (mem_iSupDirected a hdir).mpr ⟨i, hZ⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood

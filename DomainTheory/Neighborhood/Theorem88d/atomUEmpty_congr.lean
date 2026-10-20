/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)





























theorem atomUEmpty_congr {n k k' : ℕ} (h : ∀ i < n, deltaOf k i = deltaOf k' i) :
    atomUEmpty P n k = atomUEmpty P n k' := by
  obtain ⟨hpos, hneg, -⟩ := atomUCodeState_congr P h
  unfold atomUEmpty
  rw [hpos, hneg]

end DomainTheory.Neighborhood

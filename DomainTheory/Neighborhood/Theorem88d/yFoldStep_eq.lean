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






















































/-- Unfolding `yFoldStep` at an explicit `(n, i, acc)` triple. -/
theorem yFoldStep_eq (n i acc : ℕ) :
    yFoldStep P (Nat.pair n (Nat.pair i acc)) =
      selectFn (atomUEmpty P (n + 1) (i + 2 ^ n)) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) (i + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (i + 2 ^ n)))) := by
  unfold yFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood

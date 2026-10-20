/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)






























































theorem untagStep_cont {w : ℕ} (hdone : w.unpair.2.unpair.1 = 0) {k : ℕ}
    (ha : unnum1 w.unpair.1 = k + 1) :
    untagStep w = Nat.pair (unnum2 w.unpair.1)
      (Nat.pair 0
        (Nat.pair (Nat.pair k w.unpair.2.unpair.2.unpair.1 + 1) w.unpair.2.unpair.2.unpair.2)) := by
  unfold untagStep
  rw [hdone, selectFn_zero, ha]
  have hz : isZero (k + 1) = 0 := by unfold isZero; omega
  have hsub : k + 1 - 1 = k := by omega
  rw [hz, selectFn_zero, hsub]

end DomainTheory.Neighborhood.Exercise723

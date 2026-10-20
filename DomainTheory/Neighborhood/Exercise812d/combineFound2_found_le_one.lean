/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812c
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise718
import DomainTheory.Neighborhood.Exercise812d.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718




































































theorem combineFound2_found_le_one {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) {r0 r1 : ℕ}
    (h0 : r0.unpair.1 ≤ 1) (h1 : r1.unpair.1 ≤ 1) :
    (combineFound2 hUnion r0 r1).unpair.1 ≤ 1 := by
  unfold combineFound2
  rcases Nat.eq_zero_or_pos r0.unpair.1 with hr0 | hr0
  · rw [hr0, selectFn_zero]; exact h1
  · rw [show r0.unpair.1 = 1 from by omega, selectFn_one]
    rcases Nat.eq_zero_or_pos r1.unpair.1 with hr1 | hr1
    · rw [hr1, selectFn_zero]; exact h0
    · rw [show r1.unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]

end DomainTheory.Neighborhood

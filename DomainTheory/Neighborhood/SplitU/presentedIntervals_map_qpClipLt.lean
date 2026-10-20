/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem




theorem presentedIntervals_map_qpClipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, qpClipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

end DomainTheory.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.presentedIntervals_map_qpClipLt
import DomainTheory.Neighborhood.SplitU.presentedIntervals_decodeQPairList_clipLtListCode
import DomainTheory.Neighborhood.SplitU.mem_decodeQPairList_firstElemCode
import DomainTheory.Neighborhood.SplitU.splitU_p0_lt
import DomainTheory.Neighborhood.SplitU.splitU_mid_gt


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

















theorem UX_splitULeft (n : ℕ) :
    UX (splitULeft n) = UX n ∩ Set.Iio (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitULeft n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨(decodeRatPair (firstElemCode (canonCode n))).1, ?_, splitU_mid_gt n⟩
      exact mem_presentedIntervals.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), le_refl _, splitU_p0_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitULeft n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

end DomainTheory.Neighborhood

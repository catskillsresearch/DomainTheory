/-ai
The neighbourhood presented by splitULeft n is the neighbourhood presented by n, cut to the open ray of rationals strictly below the decoded midpoint.

The clipped list presents a U-neighbourhood: its presented intervals are the original intervals cut below the midpoint, the left endpoint of the first canonical pair lies in them and strictly below the midpoint, and the cut is bounded because it sits inside the original neighbourhood. The canonical presentation of the left half is fixed by that membership, so its presented intervals are again the clipped intervals, which are the stated cut.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.presentedIntervals_map_qpClipLt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.presentedIntervals_decodeQPairList_clipLtListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.mem_decodeQPairList_firstElemCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_p0_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_mid_gt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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

end DomainTheory.NeighbourhoodSystems

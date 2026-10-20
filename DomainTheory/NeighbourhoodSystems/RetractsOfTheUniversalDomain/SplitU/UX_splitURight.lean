module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.presentedIntervals_map_qpClipGe
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.presentedIntervals_decodeQPairList_clipGeListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.mem_decodeQPairList_firstElemCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_mid_gt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_mid_lt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

















theorem UX_splitURight (n : ℕ) :
    UX (splitURight n) = UX n ∩ Set.Ici (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitURight n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · refine ⟨decodeRat (splitMidCode n), ?_, Set.self_mem_Ici⟩
      exact mem_presentedIntervals.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), (splitU_mid_gt n).le, splitU_mid_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitURight n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

end DomainTheory.NeighbourhoodSystems

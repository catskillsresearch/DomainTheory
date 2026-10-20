module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.forall_bounds_decodeQPairList_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_min_lt_mid

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem UX_splitU2Left (n : ℕ) :
    UX (splitU2Left n) = UX n ∩ Set.Iio (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Left n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨listMinFst (decodeQPairList (canonCode n)), ?_, splitU2_min_lt_mid n⟩
      exact listMinFst_mem_presentedIntervals (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Left n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

end DomainTheory.NeighbourhoodSystems

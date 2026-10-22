module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.forall_bounds_decodeQPairList_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_tight
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2_mid_lt_max

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem UX_splitU2Right (n : ℕ) :
    UX (splitU2Right n) = UX n ∩ Set.Ici (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Right n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxgt⟩ := listMaxSnd_tight (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
        (splitU2_mid_lt_max n)
      exact ⟨x, hx, hxgt.le⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Right n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

end DomainTheory.NeighbourhoodSystems

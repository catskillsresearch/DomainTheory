module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_fixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_singleton_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UmasterIdx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem UX_UmasterIdx : UX UmasterIdx = U.master := by
  unfold UmasterIdx
  rw [UX_eq, decodeQPairList_encodeQPairList]
  have hmem : U.mem (presentedIntervals [((0 : ℚ), (1 : ℚ))]) := by
    rw [presentedIntervals_singleton_zero_one]; exact U.master_mem
  rw [canonList_fixed hmem, presentedIntervals_singleton_zero_one]

end DomainTheory.NeighbourhoodSystems

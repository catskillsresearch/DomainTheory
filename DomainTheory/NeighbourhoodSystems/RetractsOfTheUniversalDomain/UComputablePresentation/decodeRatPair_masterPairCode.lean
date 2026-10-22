module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.masterPairCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

@[simp] theorem decodeRatPair_masterPairCode : decodeRatPair masterPairCode = ((0 : ℚ), (1 : ℚ)) := by
  unfold masterPairCode decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_zeroCode, decodeRat_oneCode]

end DomainTheory.NeighbourhoodSystems

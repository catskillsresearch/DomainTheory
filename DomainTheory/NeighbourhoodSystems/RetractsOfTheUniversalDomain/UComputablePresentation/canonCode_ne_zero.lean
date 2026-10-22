module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeQPairList_canonCode_ne_nil

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- `canonCode c` is never the `0` (empty-list) code. -/
theorem canonCode_ne_zero (c : ℕ) : canonCode c ≠ 0 := by
  intro h
  exact decodeQPairList_canonCode_ne_nil c (by rw [h]; unfold decodeQPairList; rw [decodeList_zero]; rfl)

end DomainTheory.NeighbourhoodSystems

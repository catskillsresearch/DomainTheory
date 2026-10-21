/-ai
The rational-pair list decoded from a canonical code is never empty. It contains at least the fallback pair zero and one, or a genuine clipped pair.

Unfold the canonical code. If the list code is zero, the zero test selects the master-pair singleton, which decodes to a nonempty list. Otherwise the zero test reads zero, since a reading of one would make the list code zero, and the filter branch is selected. An empty decoding of that branch would make the underlying list code zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- `decodeQPairList (canonCode c)` is never empty (it always contains at least the fallback
pair `(0,1)`, or a genuine clipped pair). -/
theorem decodeQPairList_canonCode_ne_nil (c : ℕ) : decodeQPairList (canonCode c) ≠ [] := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one, decodeQPairList_masterCode]
    simp
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro hcontra
    apply hz
    have h' := hcontra
    unfold decodeQPairList at h'
    rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'

end DomainTheory.NeighbourhoodSystems

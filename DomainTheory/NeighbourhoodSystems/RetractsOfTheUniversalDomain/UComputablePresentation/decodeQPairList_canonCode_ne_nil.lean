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

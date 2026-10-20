module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.forall_lt_decodeQPairList_canonListCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem































/-- **Every pair in `decodeQPairList (canonCode c)` is non-degenerate** — both branches of
`canonCode` (the filtered list, or the `[masterPairCode]` fallback) only ever produce
`p.1 < p.2` pairs. This is what lets `splitU` (Theorem 8.8(b) Part 4) safely pick the *first*
pair of `decodeQPairList (canonCode n)` as its midpoint-split witness, with no search needed. -/
theorem forall_lt_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), p.1 < p.2 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    exact forall_lt_decodeQPairList_canonListCode c

end DomainTheory.NeighbourhoodSystems

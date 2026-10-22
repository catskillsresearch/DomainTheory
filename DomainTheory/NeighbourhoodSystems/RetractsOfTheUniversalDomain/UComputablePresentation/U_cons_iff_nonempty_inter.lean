module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_surj_UX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition reduces to non-emptiness**: since `U`'s raw intersection
`combineCode` output is *automatically* a genuine `U`-neighbourhood whenever it is non-empty
(it is always presentable and always `⊆ [0,1)`), "`∃k. Xₖ ⊆ Xₙ∩Xₘ`" holds iff `Xₙ∩Xₘ` is
non-empty (every `Xₖ` being itself non-empty rules out the `⊆ ∅` direction). -/
theorem U_cons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, UX k ⊆ UX n ∩ UX m) ↔ (UX n ∩ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (U_mem_UX k).2.1.mono hk
  · intro hne
    have hUmem : U.mem (UX n ∩ UX m) := by
      obtain ⟨-, -, hsubn⟩ := U_mem_UX n
      exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
        (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
        hne, Set.inter_subset_left.trans hsubn⟩
    obtain ⟨k, hk⟩ := U_surj_UX hUmem
    exact ⟨k, by rw [hk]⟩

end DomainTheory.NeighbourhoodSystems

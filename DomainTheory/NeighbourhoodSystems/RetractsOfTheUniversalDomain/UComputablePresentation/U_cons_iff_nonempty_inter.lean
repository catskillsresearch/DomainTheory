/-ai
An enumerated neighbourhood of U is contained in the intersection of two enumerated neighbourhoods if and only if that intersection is nonempty. A nonempty raw intersection is itself a neighbourhood of U, so consistency reduces to nonemptiness.

A contained enumerated neighbourhood is nonempty, so the intersection is nonempty. Conversely, a nonempty intersection is a neighbourhood of U: it is presented by the combined canonical codes, it is nonempty, and it lies in the unit interval because the first neighbourhood does. Surjectivity then supplies an index whose neighbourhood equals the intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_surj_UX

@[expose] public section

set_option linter.unusedSectionVars false

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

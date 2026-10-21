/-ai
If some enumerated neighbourhood is contained in the intersection of two enumerated neighbourhoods, the neighbourhood at their intersection index equals that intersection.

The hypothesis makes the intersection nonempty. The set presented by the combined canonical codes is then a neighbourhood of U, since it equals the intersection and lies in the unit interval. Unfolding the index, the canonical code realizes the canonical list, canonicalization leaves that neighbourhood unchanged, and the combined codes present the intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_fixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_decodeQPairList_canonCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_cons_iff_nonempty_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Uinter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem Uinter_spec {n m : ℕ} (h : ∃ k, UX k ⊆ UX n ∩ UX m) : UX (Uinter n m) = UX n ∩ UX m := by
  have hne : (UX n ∩ UX m).Nonempty := (U_cons_iff_nonempty_inter n m).mp h
  have hUL : U.mem (presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_combineCode]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
      (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
      hne, Set.inter_subset_left.trans hsubn⟩
  unfold Uinter UX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL,
    presentedIntervals_decodeQPairList_combineCode]

end DomainTheory.NeighbourhoodSystems

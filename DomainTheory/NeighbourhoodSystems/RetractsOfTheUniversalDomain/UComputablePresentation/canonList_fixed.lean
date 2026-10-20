module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_map_qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_filter_qpPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`canonList` is a no-op (as a set) on a list that already presents a `U`-neighbourhood.** -/
theorem canonList_fixed {L : List (ℚ × ℚ)} (h : U.mem (presentedIntervals L)) :
    presentedIntervals (canonList L) = presentedIntervals L := by
  obtain ⟨-, hne, hsub⟩ := h
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · exfalso
    have hcontra : presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 = ∅ := by
      rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos (L.map qpClip), hL,
        presentedIntervals_nil]
    rw [Set.inter_eq_left.mpr hsub] at hcontra
    exact hne.ne_empty hcontra
  · rw [canonList_eq_of_filter_eq_cons hL, ← hL, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, Set.inter_eq_left.mpr hsub]

end DomainTheory.NeighbourhoodSystems

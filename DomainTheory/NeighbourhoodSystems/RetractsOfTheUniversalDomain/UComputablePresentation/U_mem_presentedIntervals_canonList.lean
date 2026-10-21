/-ai
The intervals presented by the canonical list of any list of rational pairs form a neighbourhood of U.

If clipping and discarding degenerate pairs leaves nothing, the canonical list is the singleton of zero and one, whose presented set is the master neighbourhood. If a head and tail remain, the canonical list is that list. Its presented set equals the original presented set cut by the unit interval, so it lies in the unit interval, and the left endpoint of its nondegenerate head lies in it, so it is nonempty and presented by that list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_map_qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.presentedIntervals_filter_qpPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_eq_of_filter_eq_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`canonList` always presents a genuine `U`-neighbourhood.** -/
theorem U_mem_presentedIntervals_canonList (L : List (ℚ × ℚ)) :
    U.mem (presentedIntervals (canonList L)) := by
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · rw [canonList_eq_of_filter_eq_nil hL]
    have heq : presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
      rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]; rfl
    rw [heq]; exact U.master_mem
  · rw [canonList_eq_of_filter_eq_cons hL]
    have hL'eq : presentedIntervals (a :: l) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
      rw [← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
    have hmem : a ∈ (L.map qpClip).filter (fun p => decide (p.1 < p.2)) := by
      rw [hL]; exact List.mem_cons.mpr (Or.inl rfl)
    have ha : a.1 < a.2 := by simpa using (List.mem_filter.mp hmem).2
    refine ⟨⟨a :: l, rfl⟩, ?_, hL'eq ▸ Set.inter_subset_right⟩
    exact ⟨a.1, mem_presentedIntervals.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _, ha⟩⟩

end DomainTheory.NeighbourhoodSystems

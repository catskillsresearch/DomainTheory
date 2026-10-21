/-ai
Mapping the upward clip at m over a list of rational pairs presents the intervals of the original list, cut to the closed ray from m.

A point of a clipped pair still lies in the original interval, because the left endpoint only rises, and it lies at or above m. Conversely, a point of an original interval that lies at or above m lies in the interval whose left endpoint is the maximum of the old left endpoint and m.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem presentedIntervals_map_qpClipGe (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipGe m)) = presentedIntervals L ∩ Set.Ici m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ici, qpClipGe]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2⟩, le_sup_right.trans hx1⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1 ⊔ m, q.2), ⟨q, hq, rfl⟩, sup_le hxq1 hxm, hxq2⟩

end DomainTheory.NeighbourhoodSystems

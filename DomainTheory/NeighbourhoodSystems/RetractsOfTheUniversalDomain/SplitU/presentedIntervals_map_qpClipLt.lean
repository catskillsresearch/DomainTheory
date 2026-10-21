/-ai
Mapping the downward clip at m over a list of rational pairs presents the intervals of the original list, cut to the open ray below m.

A point of a clipped pair still lies in the original interval, because the right endpoint only falls, and it lies strictly below m. Conversely, a point of an original interval that lies strictly below m lies in the interval whose right endpoint is the minimum of the old right endpoint and m.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem presentedIntervals_map_qpClipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, qpClipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

end DomainTheory.NeighbourhoodSystems

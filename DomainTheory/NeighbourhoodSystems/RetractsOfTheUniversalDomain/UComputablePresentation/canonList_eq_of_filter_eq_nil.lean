module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Unfolding equation for `canonList` on the `nil` branch, stated so `rw` can fire on a literal
occurrence of `canonList L` (rather than needing to see through the `match`). -/
theorem canonList_eq_of_filter_eq_nil {L : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = []) :
    canonList L = [((0 : ℚ), (1 : ℚ))] := by
  unfold canonList; rw [h]

end DomainTheory.NeighbourhoodSystems

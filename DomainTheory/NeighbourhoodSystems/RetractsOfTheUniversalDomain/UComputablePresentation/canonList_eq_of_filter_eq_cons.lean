/-ai
If clipping a list and keeping the nondegenerate pairs yields a head and tail, the canonical list equals that list.

Unfold the canonical list and rewrite by that equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Unfolding equation for `canonList` on the `cons` branch. -/
theorem canonList_eq_of_filter_eq_cons {L : List (ℚ × ℚ)} {a : ℚ × ℚ} {l : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = a :: l) :
    canonList L = a :: l := by
  unfold canonList; rw [h]

end DomainTheory.NeighbourhoodSystems

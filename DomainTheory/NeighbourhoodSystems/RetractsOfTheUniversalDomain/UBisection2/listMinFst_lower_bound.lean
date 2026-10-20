module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_le

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`listMinFst L` lower-bounds `presentedIntervals L`.** -/
theorem listMinFst_lower_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    listMinFst L ≤ x := by
  obtain ⟨p, hp, hx1, -⟩ := mem_presentedIntervals.mp hx
  exact (listMinFst_le hp).trans hx1

end DomainTheory.NeighbourhoodSystems

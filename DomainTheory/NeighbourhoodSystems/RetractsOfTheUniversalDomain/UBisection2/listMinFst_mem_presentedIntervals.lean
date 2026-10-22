module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_attained

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`listMinFst L` is the genuine minimum of `presentedIntervals L`** (membership half). -/
theorem listMinFst_mem_presentedIntervals {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) :
    listMinFst L ∈ presentedIntervals L := by
  have hub : ∀ p ∈ L, p.1 < 1 := fun p hp => (hpos p hp).trans_le (hb p hp).2
  obtain ⟨p, hp, hpeq⟩ := listMinFst_attained hne hub
  exact mem_presentedIntervals.mpr ⟨p, hp, hpeq.le, hpeq ▸ hpos p hp⟩

end DomainTheory.NeighbourhoodSystems

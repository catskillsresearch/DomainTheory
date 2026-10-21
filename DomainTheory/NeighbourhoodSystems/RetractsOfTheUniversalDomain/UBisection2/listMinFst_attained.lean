/-ai
If a list of rational pairs is nonempty and every first component is strictly below one, then some pair has first component equal to the minimum first component of the list.

The fold from seed one equals one or equals the first component of some pair. The first alternative contradicts the strict bound on a pair given by nonemptiness, using that the minimum is at most every first component. The second alternative is the required pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_minFst_mem_or_eq_seed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem listMinFst_attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hub : ∀ p ∈ L, p.1 < 1) :
    ∃ p ∈ L, p.1 = listMinFst L := by
  rcases foldl_minFst_mem_or_eq_seed L 1 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMinFst_le hp0) (not_le.mpr (hub p0 hp0))
  · exact ⟨p, hp, h1.symm⟩

end DomainTheory.NeighbourhoodSystems

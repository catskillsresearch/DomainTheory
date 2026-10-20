module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_maxSnd_mem_or_eq_seed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_ge

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem listMaxSnd_attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hlb : ∀ p ∈ L, 0 < p.2) :
    ∃ p ∈ L, p.2 = listMaxSnd L := by
  rcases foldl_maxSnd_mem_or_eq_seed L 0 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMaxSnd_ge hp0) (not_le.mpr (hlb p0 hp0))
  · exact ⟨p, hp, h1.symm⟩

end DomainTheory.NeighbourhoodSystems

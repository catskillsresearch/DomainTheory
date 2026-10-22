module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.le_pair_left

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

/-- `n.unpair.1 ≤ n` (choice-free); the decreasing measure for `Vsharp`'s left child. -/
theorem unpair_fst_le (n : ℕ) : n.unpair.1 ≤ n := by
  have h := le_pair_left n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h

end Proposition77

end DomainTheory.NeighbourhoodSystems

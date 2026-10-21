/-ai
The neighbourhood indexed by zero is the set of all natural numbers.

Zero has every bit unset, so every natural number satisfies the membership condition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- `nbhd 0 = ℕ = Δ`: `0` has no set bits, so its excluded set `E₀` is empty. -/
theorem nbhd_zero : nbhd 0 = Set.univ := by
  ext k; simp [nbhd, Nat.zero_testBit]

end DomainTheory.NeighbourhoodSystems.Example78

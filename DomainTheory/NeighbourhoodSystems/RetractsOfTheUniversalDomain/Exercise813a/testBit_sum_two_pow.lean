module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.GeneratedBy

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`(∑ j ∈ s, 2^j).testBit i ↔ i ∈ s`.** The general "read off a prescribed finite bit pattern"
fact behind `upsample` (`Exercise812.lean`) — isolated here for reuse. -/
theorem testBit_sum_two_pow {s : Finset ℕ} {i : ℕ} : (∑ j ∈ s, 2 ^ j).testBit i ↔ i ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

end DomainTheory.NeighbourhoodSystems

/-ai
The i-th binary digit of the sum of the powers of two indexed by a finite set of natural numbers is set if and only if that index belongs to the set.

Rewrite the digit test as membership in the list of bit indices, then as membership in the finset of that list, and apply the identity that this finset, for the sum of those powers of two, is the index set itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.GeneratedBy

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`(∑ j ∈ s, 2^j).testBit i ↔ i ∈ s`.** The general "read off a prescribed finite bit pattern"
fact behind `upsample` (`Exercise812.lean`) — isolated here for reuse. -/
theorem testBit_sum_two_pow {s : Finset ℕ} {i : ℕ} : (∑ j ∈ s, 2 ^ j).testBit i ↔ i ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

end DomainTheory.NeighbourhoodSystems
